//! The mapping from RDF graphs to OWL 2 ontologies (OWL 2 Mapping to RDF
//! Graphs, 2012, §3), for graphs whose axioms and annotations carry no
//! annotations of their own.
//!
//! Declarations are read first and fix which IRIs name object, data and
//! annotation properties and datatypes, together with the built-in vocabulary.
//! The ontology header follows: an IRI typed `owl:Ontology` with its version
//! IRI, imports and annotations. Every other triple that can start an axiom is
//! then read in graph order, together with the blank nodes of its class
//! expressions, data ranges, inverse properties and lists, and every triple
//! read is marked used. The mapping succeeds only when every triple is used or
//! repeats a used one, and it returns the blank nodes it read for expressions,
//! lists and axiom nodes in the order in which the forward mapping of the
//! result allocates them. `None` means that the graph is not the image of such
//! an ontology under the forward mapping (§2), that the type of an entity is
//! missing or ambiguous, or that a cardinality exceeds `usize`.
#![allow(
    clippy::ptr_arg,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::question_mark,
    clippy::manual_map,
    clippy::collapsible_match,
    clippy::len_zero,
    clippy::needless_return,
    clippy::large_enum_variant,
    clippy::match_like_matches_macro,
    clippy::if_same_then_else,
    clippy::type_complexity
)] // Indexed operations, explicit branches and pushes for the pinned extraction subset.

use crate::builtins::builtin_kind;
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationProperty, AnnotationSubject, AnnotationValue,
    AnonymousIndividual, AtLeastTwo, Axiom, Class, ClassExpression, DataProperty, DataRange,
    Datatype, Entity, FacetRestriction, Individual, Iri, Literal, NamedIndividual, NonEmpty,
    ObjectProperty, ObjectPropertyExpression, OntologyIdentity, RawOntology,
    SubObjectPropertyExpression,
};
use crate::nnf::copy_bytes;
use crate::probes::Natural;
use crate::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfLiteral, Subject, Triple};
use crate::typing::EntityKind;

/// An ontology read from a graph, and the blank nodes the forward mapping of
/// its axioms allocates, in allocation order.
pub struct Mapped {
    pub ontology: RawOntology,
    pub blanks: Vec<BlankNode>,
}

/// Which triples are read, the blank nodes read so far, and the positions of
/// the triples whose subject is a blank node, bucketed by the hash of that
/// node in ascending order.
pub struct State {
    pub used: Vec<bool>,
    pub blanks: Vec<BlankNode>,
    pub subjects: Vec<Vec<usize>>,
}

/// A declared IRI and its kind.
pub struct Declared {
    pub iri: Vec<u8>,
    pub kind: EntityKind,
}

/// The declarations, bucketed by the hash of the IRI.
pub struct Kinds {
    pub buckets: Vec<Vec<Declared>>,
}

/// The kind of a property.
pub enum PropertyKind {
    Object,
    Data,
    Annotation,
}

/// What one triple starts.
pub enum Read {
    Skip(State),
    Found(Axiom, State),
    Fail,
}

fn equal_from(left: &Vec<u8>, right: &[u8], index: usize) -> bool {
    if index < right.len() {
        if index < left.len() {
            if left[index] == right[index] {
                equal_from(left, right, index + 1)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether the bytes spell `name`.
fn same(left: &Vec<u8>, name: &[u8]) -> bool {
    if left.len() == name.len() {
        equal_from(left, name, 0)
    } else {
        false
    }
}

fn equal_vec_from(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> bool {
    if index < right.len() {
        if index < left.len() {
            if left[index] == right[index] {
                equal_vec_from(left, right, index + 1)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether two byte strings are equal.
fn same_vec(left: &Vec<u8>, right: &Vec<u8>) -> bool {
    if left.len() == right.len() {
        equal_vec_from(left, right, 0)
    } else {
        false
    }
}

fn same_blank(left: &BlankNode, right: &BlankNode) -> bool {
    if same_vec(&left.scope, &right.scope) {
        same_vec(&left.label, &right.label)
    } else {
        false
    }
}

fn same_literal(left: &RdfLiteral, right: &RdfLiteral) -> bool {
    if same_vec(&left.lexical, &right.lexical) {
        match (&left.kind, &right.kind) {
            (LiteralKind::Datatype(a), LiteralKind::Datatype(b)) => {
                same_vec(&a.spelling, &b.spelling)
            }
            (LiteralKind::Language(a), LiteralKind::Language(b)) => same_vec(a, b),
            _ => false,
        }
    } else {
        false
    }
}

fn same_subject(left: &Subject, right: &Subject) -> bool {
    match (left, right) {
        (Subject::Iri(a), Subject::Iri(b)) => same_vec(&a.spelling, &b.spelling),
        (Subject::Blank(a), Subject::Blank(b)) => same_blank(a, b),
        _ => false,
    }
}

fn same_object(left: &Object, right: &Object) -> bool {
    match (left, right) {
        (Object::Iri(a), Object::Iri(b)) => same_vec(&a.spelling, &b.spelling),
        (Object::Blank(a), Object::Blank(b)) => same_blank(a, b),
        (Object::Literal(a), Object::Literal(b)) => same_literal(a, b),
        _ => false,
    }
}

/// Whether two triples are equal.
fn same_triple(left: &Triple, right: &Triple) -> bool {
    if same_subject(&left.subject, &right.subject) {
        if same_vec(&left.predicate.spelling, &right.predicate.spelling) {
            same_object(&left.object, &right.object)
        } else {
            false
        }
    } else {
        false
    }
}

fn copy_blank(node: &BlankNode) -> BlankNode {
    BlankNode {
        scope: copy_bytes(&node.scope),
        label: copy_bytes(&node.label),
    }
}

fn iri_of(spelling: &Vec<u8>) -> Iri {
    Iri {
        spelling: copy_bytes(spelling),
    }
}

/// The subject as a node.
fn subject_node(subject: &Subject) -> Object {
    match subject {
        Subject::Iri(iri) => Object::Iri(crate::rdf::RdfIri {
            spelling: copy_bytes(&iri.spelling),
        }),
        Subject::Blank(node) => Object::Blank(copy_blank(node)),
    }
}

/// The most buckets of an index.
const BUCKET_LIMIT: usize = 1 << 20;

/// The number of buckets for `count` entries: one more, at most `BUCKET_LIMIT`.
fn bucket_count(count: usize) -> usize {
    if count < BUCKET_LIMIT {
        count + 1
    } else {
        BUCKET_LIMIT
    }
}

/// `(hash mod 2^24) * 31 + byte`, without overflow.
fn mix(hash: usize, byte: u8) -> usize {
    (hash % 16777216) * 31 + byte as usize
}

/// The hash of `bytes[index..]` continued from `hash`.
fn hash_from(bytes: &Vec<u8>, index: usize, hash: usize) -> usize {
    if index < bytes.len() {
        hash_from(bytes, index + 1, mix(hash, bytes[index]))
    } else {
        hash
    }
}

/// The hash of a blank node: of its scope, then of its label.
fn hash_blank(node: &BlankNode) -> usize {
    hash_from(&node.label, 0, hash_from(&node.scope, 0, 7))
}

/// The hash of an IRI spelling.
fn hash_iri(spelling: &Vec<u8>) -> usize {
    hash_from(spelling, 0, 7)
}

/// The bucket of a hash among `count` buckets.
fn bucket_of(hash: usize, count: usize) -> usize {
    if 0 < count {
        hash % count
    } else {
        0
    }
}

/// `out` followed by empty buckets up to `count` buckets.
fn empty_buckets<T>(count: usize, mut out: Vec<Vec<T>>) -> Vec<Vec<T>> {
    if out.len() < count {
        out.push(Vec::new());
        empty_buckets(count, out)
    } else {
        out
    }
}

/// The buckets with the positions of the triples of `triples[index..]` whose
/// subject is a blank node added to the bucket of that node.
fn subjects_from(
    triples: &Vec<Triple>,
    index: usize,
    mut buckets: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if index < triples.len() {
        match &triples[index].subject {
            Subject::Blank(node) => {
                let bucket = bucket_of(hash_blank(node), buckets.len());
                if bucket < buckets.len() {
                    if buckets[bucket].len() < usize::MAX {
                        buckets[bucket].push(index);
                    }
                }
                subjects_from(triples, index + 1, buckets)
            }
            Subject::Iri(_) => subjects_from(triples, index + 1, buckets),
        }
    } else {
        buckets
    }
}

fn is_used(used: &Vec<bool>, index: usize) -> bool {
    if index < used.len() {
        used[index]
    } else {
        true
    }
}

/// The state with the triple at `index` marked used.
fn take(mut state: State, index: usize) -> State {
    if index < state.used.len() {
        state.used[index] = true;
    }
    state
}

/// The state with `node` recorded as the next blank node read.
fn record(mut state: State, node: &BlankNode) -> State {
    state.blanks.push(copy_blank(node));
    state
}

/// Whether the triple's subject is the blank node.
fn about(triple: &Triple, node: &BlankNode) -> bool {
    match &triple.subject {
        Subject::Blank(subject) => same_blank(subject, node),
        Subject::Iri(_) => false,
    }
}

/// Whether the triple at `index` is unused, about `node` and has the
/// predicate `name`.
fn fits(
    triples: &Vec<Triple>,
    used: &Vec<bool>,
    index: usize,
    node: &BlankNode,
    name: &[u8],
) -> bool {
    if index < triples.len() {
        if is_used(used, index) {
            false
        } else if about(&triples[index], node) {
            same(&triples[index].predicate.spelling, name)
        } else {
            false
        }
    } else {
        false
    }
}

/// The first position of `bucket[k..]` whose triple is unused, about `node`
/// and has the predicate `name`.
fn find_in(
    triples: &Vec<Triple>,
    used: &Vec<bool>,
    bucket: &Vec<usize>,
    node: &BlankNode,
    name: &[u8],
    k: usize,
) -> Option<usize> {
    if k < bucket.len() {
        if fits(triples, used, bucket[k], node, name) {
            Some(bucket[k])
        } else {
            find_in(triples, used, bucket, node, name, k + 1)
        }
    } else {
        None
    }
}

/// The first unused triple about `node` with predicate `name`, among the
/// triples of its bucket.
fn find(triples: &Vec<Triple>, state: &State, node: &BlankNode, name: &[u8]) -> Option<usize> {
    let bucket = bucket_of(hash_blank(node), state.subjects.len());
    if bucket < state.subjects.len() {
        find_in(triples, &state.used, &state.subjects[bucket], node, name, 0)
    } else {
        None
    }
}

/// Whether the object is the IRI `name`.
fn object_is(object: &Object, name: &[u8]) -> bool {
    match object {
        Object::Iri(iri) => same(&iri.spelling, name),
        _ => false,
    }
}

/// Whether the triple at `index` is unused and types `node` as `name`.
fn fits_type(
    triples: &Vec<Triple>,
    used: &Vec<bool>,
    index: usize,
    node: &BlankNode,
    name: &[u8],
) -> bool {
    if index < triples.len() {
        if is_used(used, index) {
            false
        } else if about(&triples[index], node) {
            if same(
                &triples[index].predicate.spelling,
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
            ) {
                object_is(&triples[index].object, name)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// The first position of `bucket[k..]` whose triple is unused and types
/// `node` as `name`.
fn find_type_in(
    triples: &Vec<Triple>,
    used: &Vec<bool>,
    bucket: &Vec<usize>,
    node: &BlankNode,
    name: &[u8],
    k: usize,
) -> Option<usize> {
    if k < bucket.len() {
        if fits_type(triples, used, bucket[k], node, name) {
            Some(bucket[k])
        } else {
            find_type_in(triples, used, bucket, node, name, k + 1)
        }
    } else {
        None
    }
}

/// The first unused triple that types `node` as `name`, among the triples of
/// its bucket.
fn find_type(triples: &Vec<Triple>, state: &State, node: &BlankNode, name: &[u8]) -> Option<usize> {
    let bucket = bucket_of(hash_blank(node), state.subjects.len());
    if bucket < state.subjects.len() {
        find_type_in(triples, &state.used, &state.subjects[bucket], node, name, 0)
    } else {
        None
    }
}

/// Whether the triple at `index` is unused and about `node`.
fn fits_any(triples: &Vec<Triple>, used: &Vec<bool>, index: usize, node: &BlankNode) -> bool {
    if index < triples.len() {
        if is_used(used, index) {
            false
        } else {
            about(&triples[index], node)
        }
    } else {
        false
    }
}

/// The first position of `bucket[k..]` whose triple is unused and about `node`.
fn find_any_in(
    triples: &Vec<Triple>,
    used: &Vec<bool>,
    bucket: &Vec<usize>,
    node: &BlankNode,
    k: usize,
) -> Option<usize> {
    if k < bucket.len() {
        if fits_any(triples, used, bucket[k], node) {
            Some(bucket[k])
        } else {
            find_any_in(triples, used, bucket, node, k + 1)
        }
    } else {
        None
    }
}

/// The first unused triple about `node`, among the triples of its bucket.
fn find_any(triples: &Vec<Triple>, state: &State, node: &BlankNode) -> Option<usize> {
    let bucket = bucket_of(hash_blank(node), state.subjects.len());
    if bucket < state.subjects.len() {
        find_any_in(triples, &state.used, &state.subjects[bucket], node, 0)
    } else {
        None
    }
}

/// Whether `bucket[index..]` declares the IRI with the kind.
fn declared_in(bucket: &Vec<Declared>, iri: &Vec<u8>, kind: &EntityKind, index: usize) -> bool {
    if index < bucket.len() {
        if same_vec(&bucket[index].iri, iri) {
            if same_kind(&bucket[index].kind, kind) {
                true
            } else {
                declared_in(bucket, iri, kind, index + 1)
            }
        } else {
            declared_in(bucket, iri, kind, index + 1)
        }
    } else {
        false
    }
}

/// Whether the declarations in the bucket of the IRI declare it with the kind.
fn declared(kinds: &Kinds, iri: &Vec<u8>, kind: &EntityKind) -> bool {
    let bucket = bucket_of(hash_iri(iri), kinds.buckets.len());
    if bucket < kinds.buckets.len() {
        declared_in(&kinds.buckets[bucket], iri, kind, 0)
    } else {
        false
    }
}

fn same_kind(left: &EntityKind, right: &EntityKind) -> bool {
    match (left, right) {
        (EntityKind::Class, EntityKind::Class) => true,
        (EntityKind::Datatype, EntityKind::Datatype) => true,
        (EntityKind::ObjectProperty, EntityKind::ObjectProperty) => true,
        (EntityKind::DataProperty, EntityKind::DataProperty) => true,
        (EntityKind::AnnotationProperty, EntityKind::AnnotationProperty) => true,
        (EntityKind::NamedIndividual, EntityKind::NamedIndividual) => true,
        _ => false,
    }
}

/// Whether the IRI has the kind by declaration or as built-in vocabulary.
fn has_kind(kinds: &Kinds, iri: &Vec<u8>, kind: &EntityKind) -> bool {
    if declared(kinds, iri, kind) {
        true
    } else {
        match builtin_kind(iri) {
            Some(builtin) => same_kind(&builtin, kind),
            None => false,
        }
    }
}

/// The one kind of property the IRI names; `None` when it names none or more
/// than one.
fn property_kind(kinds: &Kinds, iri: &Vec<u8>) -> Option<PropertyKind> {
    let object = has_kind(kinds, iri, &EntityKind::ObjectProperty);
    let data = has_kind(kinds, iri, &EntityKind::DataProperty);
    let annotation = has_kind(kinds, iri, &EntityKind::AnnotationProperty);
    if object {
        if data {
            None
        } else if annotation {
            None
        } else {
            Some(PropertyKind::Object)
        }
    } else if data {
        if annotation {
            None
        } else {
            Some(PropertyKind::Data)
        }
    } else if annotation {
        Some(PropertyKind::Annotation)
    } else {
        None
    }
}

/// The kind of the property a node names: a blank node is an inverse object
/// property expression.
fn node_kind(kinds: &Kinds, node: &Object) -> Option<PropertyKind> {
    match node {
        Object::Iri(iri) => property_kind(kinds, &iri.spelling),
        Object::Blank(_) => Some(PropertyKind::Object),
        Object::Literal(_) => None,
    }
}

/// The largest cardinality read; larger ones get no answer.
const CARDINALITY_LIMIT: usize = 10_000;

/// `out` followed by `name[index..]`.
fn spelled(name: &[u8], index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < name.len() {
        if out.len() < usize::MAX {
            out.push(name[index]);
        }
        spelled(name, index + 1, out)
    } else {
        out
    }
}

fn has_at(bytes: &Vec<u8>, index: usize) -> bool {
    if index < bytes.len() {
        if bytes[index] == 64 {
            true
        } else {
            has_at(bytes, index + 1)
        }
    } else {
        false
    }
}

fn append_from(mut out: Vec<u8>, bytes: &Vec<u8>, index: usize) -> Vec<u8> {
    if index < bytes.len() {
        if out.len() < usize::MAX {
            out.push(bytes[index]);
        }
        append_from(out, bytes, index + 1)
    } else {
        out
    }
}

/// The structural literal of an RDF literal: a language-tagged literal becomes
/// the `rdf:PlainLiteral` with the tag after the last `@`; no literal typed
/// `rdf:PlainLiteral` and no empty tag or tag with `@` is the image of one.
fn literal_of(literal: &RdfLiteral) -> Option<Literal> {
    match &literal.kind {
        LiteralKind::Datatype(datatype) => {
            if same(
                &datatype.spelling,
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
            ) {
                None
            } else {
                Some(Literal {
                    lexical: copy_bytes(&literal.lexical),
                    datatype: Datatype {
                        iri: iri_of(&datatype.spelling),
                    },
                })
            }
        }
        LiteralKind::Language(tag) => {
            if tag.len() == 0 {
                None
            } else if has_at(tag, 0) {
                None
            } else if literal.lexical.len() < usize::MAX - tag.len() {
                let mut lexical = copy_bytes(&literal.lexical);
                lexical.push(64);
                Some(Literal {
                    lexical: append_from(lexical, tag, 0),
                    datatype: Datatype {
                        iri: Iri {
                            spelling: spelled(
                                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
                                0,
                                Vec::new(),
                            ),
                        },
                    },
                })
            } else {
                None
            }
        }
    }
}

/// The literal a node is.
fn node_literal(node: &Object) -> Option<Literal> {
    match node {
        Object::Literal(literal) => literal_of(literal),
        _ => None,
    }
}

fn natural_up(count: usize, out: Natural) -> Natural {
    if count == 0 {
        out
    } else {
        natural_up(count - 1, Natural::Succ(Box::new(out)))
    }
}

/// The cardinality a node spells: a canonical `xsd:nonNegativeInteger` literal
/// of at most `CARDINALITY_LIMIT`.
fn node_natural(node: &Object) -> Option<Natural> {
    match node {
        Object::Literal(literal) => match &literal.kind {
            LiteralKind::Datatype(datatype) => {
                if same(
                    &datatype.spelling,
                    b"http://www.w3.org/2001/XMLSchema#nonNegativeInteger",
                ) {
                    if literal.lexical.len() > 1 {
                        if literal.lexical[0] == 48 {
                            return None;
                        }
                    }
                    match crate::decimal::read_bounded(
                        &literal.lexical,
                        0,
                        literal.lexical.len(),
                        CARDINALITY_LIMIT,
                    ) {
                        Some(value) => Some(natural_up(value, Natural::Zero)),
                        None => None,
                    }
                } else {
                    None
                }
            }
            LiteralKind::Language(_) => None,
        },
        _ => None,
    }
}

/// Whether the node is the literal `"true"^^xsd:boolean`.
fn node_true(node: &Object) -> bool {
    match node {
        Object::Literal(literal) => match &literal.kind {
            LiteralKind::Datatype(datatype) => {
                if same(
                    &datatype.spelling,
                    b"http://www.w3.org/2001/XMLSchema#boolean",
                ) {
                    same(&literal.lexical, b"true")
                } else {
                    false
                }
            }
            LiteralKind::Language(_) => false,
        },
        _ => false,
    }
}

/// The individual a node names: an IRI or a blank node.
fn node_individual(node: &Object) -> Option<Individual> {
    match node {
        Object::Iri(iri) => Some(Individual::Named(NamedIndividual {
            iri: iri_of(&iri.spelling),
        })),
        Object::Blank(node) => Some(Individual::Anonymous(AnonymousIndividual {
            scope: copy_bytes(&node.scope),
            label: copy_bytes(&node.label),
        })),
        Object::Literal(_) => None,
    }
}

/// The IRI a node is.
fn node_iri(node: &Object) -> Option<Iri> {
    match node {
        Object::Iri(iri) => Some(iri_of(&iri.spelling)),
        _ => None,
    }
}

/// The object property expression a node names: an IRI, or a blank node with
/// one `owl:inverseOf` triple.
fn property_expression(
    triples: &Vec<Triple>,
    node: &Object,
    state: State,
) -> Option<(ObjectPropertyExpression, State)> {
    match node {
        Object::Iri(iri) => Some((
            ObjectPropertyExpression::Property(ObjectProperty {
                iri: iri_of(&iri.spelling),
            }),
            state,
        )),
        Object::Blank(blank) => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#inverseOf",
        ) {
            Some(index) => match &triples[index].object {
                Object::Iri(iri) => {
                    let state = take(state, index);
                    let state = record(state, blank);
                    Some((
                        ObjectPropertyExpression::Inverse(ObjectProperty {
                            iri: iri_of(&iri.spelling),
                        }),
                        state,
                    ))
                }
                _ => None,
            },
            None => None,
        },
        Object::Literal(_) => None,
    }
}

/// The list cell a node is: its `rdf:first` and `rdf:rest` triples, used, and
/// the cell recorded.
fn cell(triples: &Vec<Triple>, node: &Object, state: State) -> Option<(usize, usize, State)> {
    match node {
        Object::Blank(blank) => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#first",
        ) {
            Some(first) => {
                let state = take(state, first);
                match find(
                    triples,
                    &state,
                    blank,
                    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest",
                ) {
                    Some(rest) => {
                        let state = take(state, rest);
                        let state = record(state, blank);
                        Some((first, rest, state))
                    }
                    None => None,
                }
            }
            None => None,
        },
        _ => None,
    }
}

/// Whether the node is `rdf:nil`.
fn is_nil(node: &Object) -> bool {
    object_is(node, b"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil")
}

/// The cells of the list a node starts, recorded in order: `out` followed by
/// the indices of their `rdf:first` triples.
fn cells(
    triples: &Vec<Triple>,
    node: &Object,
    state: State,
    mut out: Vec<usize>,
    fuel: usize,
) -> Option<(Vec<usize>, State)> {
    if is_nil(node) {
        Some((out, state))
    } else if fuel > 0 {
        match cell(triples, node, state) {
            Some((first, rest, state)) => {
                if out.len() < usize::MAX {
                    out.push(first);
                    cells(triples, &triples[rest].object, state, out, fuel - 1)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        None
    }
}

/// The element node of the list cell whose `rdf:first` triple is `first`.
fn element(triples: &Vec<Triple>, first: usize) -> Option<&Object> {
    if first < triples.len() {
        Some(&triples[first].object)
    } else {
        None
    }
}

/// `out` followed by the class expressions of `firsts[index..]`.
fn class_members(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
    mut out: Vec<ClassExpression>,
    fuel: usize,
) -> Option<(Vec<ClassExpression>, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match class_expression(triples, kinds, node, state, fuel) {
                Some((member, state)) => {
                    if out.len() < usize::MAX {
                        out.push(member);
                        class_members(triples, kinds, firsts, index + 1, state, out, fuel)
                    } else {
                        None
                    }
                }
                None => None,
            },
            None => None,
        }
    } else {
        Some((out, state))
    }
}

/// The class expressions of a list of at least two.
fn class_list2(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(AtLeastTwo<ClassExpression>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => {
            if firsts.len() >= 2 {
                match element(triples, firsts[0]) {
                    Some(one) => match class_expression(triples, kinds, one, state, fuel) {
                        Some((first, state)) => match element(triples, firsts[1]) {
                            Some(two) => match class_expression(triples, kinds, two, state, fuel) {
                                Some((second, state)) => {
                                    match class_members(
                                        triples,
                                        kinds,
                                        &firsts,
                                        2,
                                        state,
                                        Vec::new(),
                                        fuel,
                                    ) {
                                        Some((rest, state)) => Some((
                                            AtLeastTwo {
                                                first,
                                                second,
                                                rest,
                                            },
                                            state,
                                        )),
                                        None => None,
                                    }
                                }
                                None => None,
                            },
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// `out` followed by the individuals of `firsts[index..]`.
fn individual_members(
    triples: &Vec<Triple>,
    firsts: &Vec<usize>,
    index: usize,
    mut out: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_individual(node) {
                Some(member) => {
                    if out.len() < usize::MAX {
                        out.push(member);
                        individual_members(triples, firsts, index + 1, out)
                    } else {
                        None
                    }
                }
                None => None,
            },
            None => None,
        }
    } else {
        Some(out)
    }
}

/// The individuals of a nonempty list.
fn individual_list1(
    triples: &Vec<Triple>,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(NonEmpty<Individual>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => {
            if firsts.len() >= 1 {
                match element(triples, firsts[0]) {
                    Some(one) => match node_individual(one) {
                        Some(first) => match individual_members(triples, &firsts, 1, Vec::new()) {
                            Some(rest) => Some((NonEmpty { first, rest }, state)),
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// The individuals of a list of at least two.
fn individual_list2(
    triples: &Vec<Triple>,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(AtLeastTwo<Individual>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => {
            if firsts.len() >= 2 {
                match element(triples, firsts[0]) {
                    Some(one) => match node_individual(one) {
                        Some(first) => match element(triples, firsts[1]) {
                            Some(two) => match node_individual(two) {
                                Some(second) => {
                                    match individual_members(triples, &firsts, 2, Vec::new()) {
                                        Some(rest) => Some((
                                            AtLeastTwo {
                                                first,
                                                second,
                                                rest,
                                            },
                                            state,
                                        )),
                                        None => None,
                                    }
                                }
                                None => None,
                            },
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// `out` followed by the literals of `firsts[index..]`.
fn literal_members(
    triples: &Vec<Triple>,
    firsts: &Vec<usize>,
    index: usize,
    mut out: Vec<Literal>,
) -> Option<Vec<Literal>> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_literal(node) {
                Some(member) => {
                    if out.len() < usize::MAX {
                        out.push(member);
                        literal_members(triples, firsts, index + 1, out)
                    } else {
                        None
                    }
                }
                None => None,
            },
            None => None,
        }
    } else {
        Some(out)
    }
}

/// The literals of a nonempty list.
fn literal_list1(
    triples: &Vec<Triple>,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(NonEmpty<Literal>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => {
            if firsts.len() >= 1 {
                match element(triples, firsts[0]) {
                    Some(one) => match node_literal(one) {
                        Some(first) => match literal_members(triples, &firsts, 1, Vec::new()) {
                            Some(rest) => Some((NonEmpty { first, rest }, state)),
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// `out` followed by the object property expressions of `firsts[index..]`.
fn property_members(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
    mut out: Vec<ObjectPropertyExpression>,
) -> Option<(Vec<ObjectPropertyExpression>, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_kind(kinds, node) {
                Some(PropertyKind::Object) => match property_expression(triples, node, state) {
                    Some((member, state)) => {
                        if out.len() < usize::MAX {
                            out.push(member);
                            property_members(triples, kinds, firsts, index + 1, state, out)
                        } else {
                            None
                        }
                    }
                    None => None,
                },
                _ => None,
            },
            None => None,
        }
    } else {
        Some((out, state))
    }
}

/// The object property expression an element node names.
fn property_element(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
) -> Option<(ObjectPropertyExpression, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_kind(kinds, node) {
                Some(PropertyKind::Object) => property_expression(triples, node, state),
                _ => None,
            },
            None => None,
        }
    } else {
        None
    }
}

/// The object property expressions of a list of at least two.
fn property_list2(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(AtLeastTwo<ObjectPropertyExpression>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => match property_element(triples, kinds, &firsts, 0, state) {
            Some((first, state)) => match property_element(triples, kinds, &firsts, 1, state) {
                Some((second, state)) => {
                    match property_members(triples, kinds, &firsts, 2, state, Vec::new()) {
                        Some((rest, state)) => Some((
                            AtLeastTwo {
                                first,
                                second,
                                rest,
                            },
                            state,
                        )),
                        None => None,
                    }
                }
                None => None,
            },
            None => None,
        },
        None => None,
    }
}

/// The data properties of `firsts[index..]`, after `out`.
fn data_members(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    mut out: Vec<DataProperty>,
) -> Option<Vec<DataProperty>> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_kind(kinds, node) {
                Some(PropertyKind::Data) => match node_iri(node) {
                    Some(iri) => {
                        if out.len() < usize::MAX {
                            out.push(DataProperty { iri });
                            data_members(triples, kinds, firsts, index + 1, out)
                        } else {
                            None
                        }
                    }
                    None => None,
                },
                _ => None,
            },
            None => None,
        }
    } else {
        Some(out)
    }
}

/// The data property an element node names.
fn data_element(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
) -> Option<DataProperty> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_kind(kinds, node) {
                Some(PropertyKind::Data) => match node_iri(node) {
                    Some(iri) => Some(DataProperty { iri }),
                    None => None,
                },
                _ => None,
            },
            None => None,
        }
    } else {
        None
    }
}

/// The data properties of a list of at least two.
fn data_list2(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(AtLeastTwo<DataProperty>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => match data_element(triples, kinds, &firsts, 0) {
            Some(first) => match data_element(triples, kinds, &firsts, 1) {
                Some(second) => match data_members(triples, kinds, &firsts, 2, Vec::new()) {
                    Some(rest) => Some((
                        AtLeastTwo {
                            first,
                            second,
                            rest,
                        },
                        state,
                    )),
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        None => None,
    }
}

/// The key properties of `firsts[index..]`: object property expressions
/// first, then data properties.
fn key_members(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
    mut objects: Vec<ObjectPropertyExpression>,
    mut datas: Vec<DataProperty>,
) -> Option<(Vec<ObjectPropertyExpression>, Vec<DataProperty>, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match node_kind(kinds, node) {
                Some(PropertyKind::Object) => {
                    if datas.len() == 0 {
                        match property_expression(triples, node, state) {
                            Some((member, state)) => {
                                if objects.len() < usize::MAX {
                                    objects.push(member);
                                    key_members(
                                        triples,
                                        kinds,
                                        firsts,
                                        index + 1,
                                        state,
                                        objects,
                                        datas,
                                    )
                                } else {
                                    None
                                }
                            }
                            None => None,
                        }
                    } else {
                        None
                    }
                }
                Some(PropertyKind::Data) => match node_iri(node) {
                    Some(iri) => {
                        if datas.len() < usize::MAX {
                            datas.push(DataProperty { iri });
                            key_members(triples, kinds, firsts, index + 1, state, objects, datas)
                        } else {
                            None
                        }
                    }
                    None => None,
                },
                _ => None,
            },
            None => None,
        }
    } else {
        Some((objects, datas, state))
    }
}

/// The class expression a node is: a class IRI, or a blank node typed
/// `owl:Restriction` or `owl:Class` with its construct.
fn class_expression(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match node {
        Object::Iri(iri) => Some((
            ClassExpression::Class(Class {
                iri: iri_of(&iri.spelling),
            }),
            state,
        )),
        Object::Blank(blank) => {
            if fuel > 0 {
                match find_type(
                    triples,
                    &state,
                    blank,
                    b"http://www.w3.org/2002/07/owl#Restriction",
                ) {
                    Some(index) => {
                        let state = take(state, index);
                        let state = record(state, blank);
                        restriction(triples, kinds, blank, state, fuel - 1)
                    }
                    None => match find_type(
                        triples,
                        &state,
                        blank,
                        b"http://www.w3.org/2002/07/owl#Class",
                    ) {
                        Some(index) => {
                            let state = take(state, index);
                            let state = record(state, blank);
                            class_construct(triples, kinds, blank, state, fuel - 1)
                        }
                        None => None,
                    },
                }
            } else {
                None
            }
        }
        Object::Literal(_) => None,
    }
}

/// The Boolean construct or enumeration of a blank node typed `owl:Class`.
fn class_construct(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#intersectionOf",
    ) {
        Some(index) => {
            let state = take(state, index);
            match class_list2(triples, kinds, &triples[index].object, state, fuel) {
                Some((members, state)) => Some((
                    ClassExpression::ObjectIntersectionOf(Box::new(members)),
                    state,
                )),
                None => None,
            }
        }
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#unionOf",
        ) {
            Some(index) => {
                let state = take(state, index);
                match class_list2(triples, kinds, &triples[index].object, state, fuel) {
                    Some((members, state)) => {
                        Some((ClassExpression::ObjectUnionOf(Box::new(members)), state))
                    }
                    None => None,
                }
            }
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#complementOf",
            ) {
                Some(index) => {
                    let state = take(state, index);
                    match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                        Some((inner, state)) => {
                            Some((ClassExpression::ObjectComplementOf(Box::new(inner)), state))
                        }
                        None => None,
                    }
                }
                None => match find(
                    triples,
                    &state,
                    blank,
                    b"http://www.w3.org/2002/07/owl#oneOf",
                ) {
                    Some(index) => {
                        let state = take(state, index);
                        match individual_list1(triples, &triples[index].object, state, fuel) {
                            Some((members, state)) => {
                                Some((ClassExpression::ObjectOneOf(members), state))
                            }
                            None => None,
                        }
                    }
                    None => None,
                },
            },
        },
    }
}

/// The restriction on the property of a blank node typed `owl:Restriction`.
fn restriction(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#onProperty",
    ) {
        Some(index) => {
            let state = take(state, index);
            let property = &triples[index].object;
            match node_kind(kinds, property) {
                Some(PropertyKind::Object) => match property_expression(triples, property, state) {
                    Some((role, state)) => {
                        object_restriction(triples, kinds, blank, role, state, fuel)
                    }
                    None => None,
                },
                Some(PropertyKind::Data) => match node_iri(property) {
                    Some(iri) => {
                        data_restriction(triples, kinds, blank, DataProperty { iri }, state, fuel)
                    }
                    None => None,
                },
                _ => None,
            }
        }
        None => None,
    }
}

/// An object restriction on `role`.
fn object_restriction(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    role: ObjectPropertyExpression,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#someValuesFrom",
    ) {
        Some(index) => {
            let state = take(state, index);
            match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                Some((filler, state)) => Some((
                    ClassExpression::ObjectSomeValuesFrom(role, Box::new(filler)),
                    state,
                )),
                None => None,
            }
        }
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#allValuesFrom",
        ) {
            Some(index) => {
                let state = take(state, index);
                match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                    Some((filler, state)) => Some((
                        ClassExpression::ObjectAllValuesFrom(role, Box::new(filler)),
                        state,
                    )),
                    None => None,
                }
            }
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#hasValue",
            ) {
                Some(index) => {
                    let state = take(state, index);
                    match node_individual(&triples[index].object) {
                        Some(value) => Some((ClassExpression::ObjectHasValue(role, value), state)),
                        None => None,
                    }
                }
                None => match find(
                    triples,
                    &state,
                    blank,
                    b"http://www.w3.org/2002/07/owl#hasSelf",
                ) {
                    Some(index) => {
                        let state = take(state, index);
                        if node_true(&triples[index].object) {
                            Some((ClassExpression::ObjectHasSelf(role), state))
                        } else {
                            None
                        }
                    }
                    None => object_cardinality(triples, kinds, blank, role, state, fuel),
                },
            },
        },
    }
}

/// An object cardinality restriction on `role`.
fn object_cardinality(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    role: ObjectPropertyExpression,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#minCardinality",
    ) {
        Some(index) => match node_natural(&triples[index].object) {
            Some(n) => Some((
                ClassExpression::ObjectMinCardinality(n, role, None),
                take(state, index),
            )),
            None => None,
        },
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#maxCardinality",
        ) {
            Some(index) => match node_natural(&triples[index].object) {
                Some(n) => Some((
                    ClassExpression::ObjectMaxCardinality(n, role, None),
                    take(state, index),
                )),
                None => None,
            },
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#cardinality",
            ) {
                Some(index) => match node_natural(&triples[index].object) {
                    Some(n) => Some((
                        ClassExpression::ObjectExactCardinality(n, role, None),
                        take(state, index),
                    )),
                    None => None,
                },
                None => object_qualified(triples, kinds, blank, role, state, fuel),
            },
        },
    }
}

/// The filler class of a qualified object cardinality restriction.
fn on_class(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#onClass",
    ) {
        Some(index) => {
            let state = take(state, index);
            class_expression(triples, kinds, &triples[index].object, state, fuel)
        }
        None => None,
    }
}

/// A qualified object cardinality restriction on `role`.
fn object_qualified(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    role: ObjectPropertyExpression,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#minQualifiedCardinality",
    ) {
        Some(index) => match node_natural(&triples[index].object) {
            Some(n) => match on_class(triples, kinds, blank, take(state, index), fuel) {
                Some((filler, state)) => Some((
                    ClassExpression::ObjectMinCardinality(n, role, Some(Box::new(filler))),
                    state,
                )),
                None => None,
            },
            None => None,
        },
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#maxQualifiedCardinality",
        ) {
            Some(index) => match node_natural(&triples[index].object) {
                Some(n) => match on_class(triples, kinds, blank, take(state, index), fuel) {
                    Some((filler, state)) => Some((
                        ClassExpression::ObjectMaxCardinality(n, role, Some(Box::new(filler))),
                        state,
                    )),
                    None => None,
                },
                None => None,
            },
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#qualifiedCardinality",
            ) {
                Some(index) => match node_natural(&triples[index].object) {
                    Some(n) => match on_class(triples, kinds, blank, take(state, index), fuel) {
                        Some((filler, state)) => Some((
                            ClassExpression::ObjectExactCardinality(
                                n,
                                role,
                                Some(Box::new(filler)),
                            ),
                            state,
                        )),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            },
        },
    }
}

/// A data restriction on `property`.
fn data_restriction(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    property: DataProperty,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#someValuesFrom",
    ) {
        Some(index) => {
            let state = take(state, index);
            match data_range(triples, kinds, &triples[index].object, state, fuel) {
                Some((range, state)) => {
                    Some((ClassExpression::DataSomeValuesFrom(property, range), state))
                }
                None => None,
            }
        }
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#allValuesFrom",
        ) {
            Some(index) => {
                let state = take(state, index);
                match data_range(triples, kinds, &triples[index].object, state, fuel) {
                    Some((range, state)) => {
                        Some((ClassExpression::DataAllValuesFrom(property, range), state))
                    }
                    None => None,
                }
            }
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#hasValue",
            ) {
                Some(index) => match node_literal(&triples[index].object) {
                    Some(value) => Some((
                        ClassExpression::DataHasValue(property, value),
                        take(state, index),
                    )),
                    None => None,
                },
                None => data_cardinality(triples, kinds, blank, property, state, fuel),
            },
        },
    }
}

/// The filler range of a qualified data cardinality restriction.
fn on_data_range(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    state: State,
    fuel: usize,
) -> Option<(DataRange, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#onDataRange",
    ) {
        Some(index) => {
            let state = take(state, index);
            data_range(triples, kinds, &triples[index].object, state, fuel)
        }
        None => None,
    }
}

/// A data cardinality restriction on `property`.
fn data_cardinality(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    property: DataProperty,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#minCardinality",
    ) {
        Some(index) => match node_natural(&triples[index].object) {
            Some(n) => Some((
                ClassExpression::DataMinCardinality(n, property, None),
                take(state, index),
            )),
            None => None,
        },
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#maxCardinality",
        ) {
            Some(index) => match node_natural(&triples[index].object) {
                Some(n) => Some((
                    ClassExpression::DataMaxCardinality(n, property, None),
                    take(state, index),
                )),
                None => None,
            },
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#cardinality",
            ) {
                Some(index) => match node_natural(&triples[index].object) {
                    Some(n) => Some((
                        ClassExpression::DataExactCardinality(n, property, None),
                        take(state, index),
                    )),
                    None => None,
                },
                None => data_qualified(triples, kinds, blank, property, state, fuel),
            },
        },
    }
}

/// A qualified data cardinality restriction on `property`.
fn data_qualified(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    property: DataProperty,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#minQualifiedCardinality",
    ) {
        Some(index) => match node_natural(&triples[index].object) {
            Some(n) => match on_data_range(triples, kinds, blank, take(state, index), fuel) {
                Some((range, state)) => Some((
                    ClassExpression::DataMinCardinality(n, property, Some(range)),
                    state,
                )),
                None => None,
            },
            None => None,
        },
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#maxQualifiedCardinality",
        ) {
            Some(index) => match node_natural(&triples[index].object) {
                Some(n) => match on_data_range(triples, kinds, blank, take(state, index), fuel) {
                    Some((range, state)) => Some((
                        ClassExpression::DataMaxCardinality(n, property, Some(range)),
                        state,
                    )),
                    None => None,
                },
                None => None,
            },
            None => match find(
                triples,
                &state,
                blank,
                b"http://www.w3.org/2002/07/owl#qualifiedCardinality",
            ) {
                Some(index) => match node_natural(&triples[index].object) {
                    Some(n) => match on_data_range(triples, kinds, blank, take(state, index), fuel)
                    {
                        Some((range, state)) => Some((
                            ClassExpression::DataExactCardinality(n, property, Some(range)),
                            state,
                        )),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            },
        },
    }
}

/// The data range a node is: a datatype IRI, or a blank node typed
/// `rdfs:Datatype` with its construct.
fn data_range(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(DataRange, State)> {
    match node {
        Object::Iri(iri) => Some((
            DataRange::Datatype(Datatype {
                iri: iri_of(&iri.spelling),
            }),
            state,
        )),
        Object::Blank(blank) => {
            if fuel > 0 {
                match find_type(
                    triples,
                    &state,
                    blank,
                    b"http://www.w3.org/2000/01/rdf-schema#Datatype",
                ) {
                    Some(index) => {
                        let state = take(state, index);
                        let state = record(state, blank);
                        range_construct(triples, kinds, blank, state, fuel - 1)
                    }
                    None => None,
                }
            } else {
                None
            }
        }
        Object::Literal(_) => None,
    }
}

/// `out` followed by the data ranges of `firsts[index..]`.
fn range_members(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
    mut out: Vec<DataRange>,
    fuel: usize,
) -> Option<(Vec<DataRange>, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => match data_range(triples, kinds, node, state, fuel) {
                Some((member, state)) => {
                    if out.len() < usize::MAX {
                        out.push(member);
                        range_members(triples, kinds, firsts, index + 1, state, out, fuel)
                    } else {
                        None
                    }
                }
                None => None,
            },
            None => None,
        }
    } else {
        Some((out, state))
    }
}

/// The data range of the element `firsts[index]`.
fn range_element(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
    fuel: usize,
) -> Option<(DataRange, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(node) => data_range(triples, kinds, node, state, fuel),
            None => None,
        }
    } else {
        None
    }
}

/// The data ranges of a list of at least two.
fn range_list2(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    node: &Object,
    state: State,
    fuel: usize,
) -> Option<(AtLeastTwo<DataRange>, State)> {
    match cells(triples, node, state, Vec::new(), fuel) {
        Some((firsts, state)) => match range_element(triples, kinds, &firsts, 0, state, fuel) {
            Some((first, state)) => match range_element(triples, kinds, &firsts, 1, state, fuel) {
                Some((second, state)) => {
                    match range_members(triples, kinds, &firsts, 2, state, Vec::new(), fuel) {
                        Some((rest, state)) => Some((
                            AtLeastTwo {
                                first,
                                second,
                                rest,
                            },
                            state,
                        )),
                        None => None,
                    }
                }
                None => None,
            },
            None => None,
        },
        None => None,
    }
}

/// The facet restriction of the blank element node `firsts[index]`: its one
/// triple, used, and the node recorded.
fn facet_element(
    triples: &Vec<Triple>,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
) -> Option<(FacetRestriction, State)> {
    if index < firsts.len() {
        match element(triples, firsts[index]) {
            Some(Object::Blank(blank)) => match find_any(triples, &state, blank) {
                Some(found) => match node_literal(&triples[found].object) {
                    Some(value) => {
                        let state = take(state, found);
                        let state = record(state, blank);
                        Some((
                            FacetRestriction {
                                facet: iri_of(&triples[found].predicate.spelling),
                                value,
                            },
                            state,
                        ))
                    }
                    None => None,
                },
                None => None,
            },
            _ => None,
        }
    } else {
        None
    }
}

/// `out` followed by the facet restrictions of `firsts[index..]`.
fn facet_members(
    triples: &Vec<Triple>,
    firsts: &Vec<usize>,
    index: usize,
    state: State,
    mut out: Vec<FacetRestriction>,
) -> Option<(Vec<FacetRestriction>, State)> {
    if index < firsts.len() {
        match facet_element(triples, firsts, index, state) {
            Some((member, state)) => {
                if out.len() < usize::MAX {
                    out.push(member);
                    facet_members(triples, firsts, index + 1, state, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some((out, state))
    }
}

/// The construct of a blank node typed `rdfs:Datatype`.
fn range_construct(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    blank: &BlankNode,
    state: State,
    fuel: usize,
) -> Option<(DataRange, State)> {
    match find(
        triples,
        &state,
        blank,
        b"http://www.w3.org/2002/07/owl#intersectionOf",
    ) {
        Some(index) => {
            let state = take(state, index);
            match range_list2(triples, kinds, &triples[index].object, state, fuel) {
                Some((members, state)) => Some((DataRange::Intersection(Box::new(members)), state)),
                None => None,
            }
        }
        None => match find(
            triples,
            &state,
            blank,
            b"http://www.w3.org/2002/07/owl#unionOf",
        ) {
            Some(index) => {
                let state = take(state, index);
                match range_list2(triples, kinds, &triples[index].object, state, fuel) {
                    Some((members, state)) => Some((DataRange::Union(Box::new(members)), state)),
                    None => None,
                }
            }
            None => {
                match find(
                    triples,
                    &state,
                    blank,
                    b"http://www.w3.org/2002/07/owl#datatypeComplementOf",
                ) {
                    Some(index) => {
                        let state = take(state, index);
                        match data_range(triples, kinds, &triples[index].object, state, fuel) {
                            Some((inner, state)) => {
                                Some((DataRange::Complement(Box::new(inner)), state))
                            }
                            None => None,
                        }
                    }
                    None => {
                        match find(
                            triples,
                            &state,
                            blank,
                            b"http://www.w3.org/2002/07/owl#oneOf",
                        ) {
                            Some(index) => {
                                let state = take(state, index);
                                match literal_list1(triples, &triples[index].object, state, fuel) {
                                    Some((members, state)) => {
                                        Some((DataRange::OneOf(members), state))
                                    }
                                    None => None,
                                }
                            }
                            None => {
                                match find(
                                    triples,
                                    &state,
                                    blank,
                                    b"http://www.w3.org/2002/07/owl#onDatatype",
                                ) {
                                    Some(index) => {
                                        match node_iri(&triples[index].object) {
                                            Some(base) => {
                                                let state = take(state, index);
                                                match find(triples, &state, blank, b"http://www.w3.org/2002/07/owl#withRestrictions") {
                                    Some(list) => {
                                        let state = take(state, list);
                                        match cells(triples, &triples[list].object, state, Vec::new(), fuel) {
                                            Some((firsts, state)) => match facet_element(triples, &firsts, 0, state) {
                                                Some((first, state)) => match facet_members(triples, &firsts, 1, state, Vec::new()) {
                                                    Some((rest, state)) => Some((
                                                        DataRange::Restriction(Datatype { iri: base }, NonEmpty { first, rest }),
                                                        state,
                                                    )),
                                                    None => None,
                                                },
                                                None => None,
                                            },
                                            None => None,
                                        }
                                    }
                                    None => None,
                                }
                                            }
                                            None => None,
                                        }
                                    }
                                    None => None,
                                }
                            }
                        }
                    }
                }
            }
        },
    }
}

/// The class expressions of the subject and object of the main triple.
fn class_pair(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Option<(ClassExpression, ClassExpression, State)> {
    let state = take(state, index);
    let subject = subject_node(&triples[index].subject);
    match class_expression(triples, kinds, &subject, state, fuel) {
        Some((left, state)) => {
            match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                Some((right, state)) => Some((left, right, state)),
                None => None,
            }
        }
        None => None,
    }
}

fn two<T>(first: T, second: T) -> AtLeastTwo<T> {
    AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }
}

fn sub_class(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    match class_pair(triples, kinds, index, state, fuel) {
        Some((sub, sup, state)) => Read::Found(Axiom::SubClassOf(sub, sup), state),
        None => Read::Fail,
    }
}

/// Whether the subject is a datatype IRI.
fn datatype_subject(kinds: &Kinds, subject: &Subject) -> bool {
    match subject {
        Subject::Iri(iri) => has_kind(kinds, &iri.spelling, &EntityKind::Datatype),
        Subject::Blank(_) => false,
    }
}

fn equivalent_class(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    if datatype_subject(kinds, &triples[index].subject) {
        let state = take(state, index);
        match &triples[index].subject {
            Subject::Iri(iri) => {
                match data_range(triples, kinds, &triples[index].object, state, fuel) {
                    Some((range, state)) => Read::Found(
                        Axiom::DatatypeDefinition(
                            Datatype {
                                iri: iri_of(&iri.spelling),
                            },
                            range,
                        ),
                        state,
                    ),
                    None => Read::Fail,
                }
            }
            Subject::Blank(_) => Read::Fail,
        }
    } else {
        match class_pair(triples, kinds, index, state, fuel) {
            Some((left, right, state)) => {
                Read::Found(Axiom::EquivalentClasses(two(left, right)), state)
            }
            None => Read::Fail,
        }
    }
}

fn disjoint_class(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    match class_pair(triples, kinds, index, state, fuel) {
        Some((left, right, state)) => Read::Found(Axiom::DisjointClasses(two(left, right)), state),
        None => Read::Fail,
    }
}

fn disjoint_union(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    match &triples[index].subject {
        Subject::Iri(iri) => {
            let state = take(state, index);
            match class_list2(triples, kinds, &triples[index].object, state, fuel) {
                Some((members, state)) => Read::Found(
                    Axiom::DisjointUnion(
                        Class {
                            iri: iri_of(&iri.spelling),
                        },
                        members,
                    ),
                    state,
                ),
                None => Read::Fail,
            }
        }
        Subject::Blank(_) => Read::Fail,
    }
}

/// The object property expressions of the subject and object of the main triple.
fn property_pair(
    triples: &Vec<Triple>,
    index: usize,
    state: State,
) -> Option<(ObjectPropertyExpression, ObjectPropertyExpression, State)> {
    let subject = subject_node(&triples[index].subject);
    match property_expression(triples, &subject, state) {
        Some((left, state)) => match property_expression(triples, &triples[index].object, state) {
            Some((right, state)) => Some((left, right, state)),
            None => None,
        },
        None => None,
    }
}

/// The data properties of the subject and object of the main triple.
fn data_pair(triples: &Vec<Triple>, index: usize) -> Option<(DataProperty, DataProperty)> {
    let subject = subject_node(&triples[index].subject);
    match node_iri(&subject) {
        Some(left) => match node_iri(&triples[index].object) {
            Some(right) => Some((DataProperty { iri: left }, DataProperty { iri: right })),
            None => None,
        },
        None => None,
    }
}

/// The kind of the property the subject of the main triple names.
fn subject_kind(triples: &Vec<Triple>, kinds: &Kinds, index: usize) -> Option<PropertyKind> {
    node_kind(kinds, &subject_node(&triples[index].subject))
}

fn sub_property(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State) -> Read {
    let state = take(state, index);
    match subject_kind(triples, kinds, index) {
        Some(PropertyKind::Object) => match property_pair(triples, index, state) {
            Some((sub, sup, state)) => Read::Found(
                Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(sub), sup),
                state,
            ),
            None => Read::Fail,
        },
        Some(PropertyKind::Data) => match data_pair(triples, index) {
            Some((sub, sup)) => Read::Found(Axiom::SubDataPropertyOf(sub, sup), state),
            None => Read::Fail,
        },
        Some(PropertyKind::Annotation) => match data_pair(triples, index) {
            Some((sub, sup)) => Read::Found(
                Axiom::SubAnnotationPropertyOf(
                    AnnotationProperty { iri: sub.iri },
                    AnnotationProperty { iri: sup.iri },
                ),
                state,
            ),
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

fn property_chain(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    let state = take(state, index);
    let subject = subject_node(&triples[index].subject);
    match property_expression(triples, &subject, state) {
        Some((sup, state)) => {
            match property_list2(triples, kinds, &triples[index].object, state, fuel) {
                Some((chain, state)) => Read::Found(
                    Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(chain), sup),
                    state,
                ),
                None => Read::Fail,
            }
        }
        None => Read::Fail,
    }
}

fn equivalent_property(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State) -> Read {
    let state = take(state, index);
    match subject_kind(triples, kinds, index) {
        Some(PropertyKind::Object) => match property_pair(triples, index, state) {
            Some((left, right, state)) => {
                Read::Found(Axiom::EquivalentObjectProperties(two(left, right)), state)
            }
            None => Read::Fail,
        },
        Some(PropertyKind::Data) => match data_pair(triples, index) {
            Some((left, right)) => {
                Read::Found(Axiom::EquivalentDataProperties(two(left, right)), state)
            }
            None => Read::Fail,
        },
        _ => Read::Fail,
    }
}

fn disjoint_property(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State) -> Read {
    let state = take(state, index);
    match subject_kind(triples, kinds, index) {
        Some(PropertyKind::Object) => match property_pair(triples, index, state) {
            Some((left, right, state)) => {
                Read::Found(Axiom::DisjointObjectProperties(two(left, right)), state)
            }
            None => Read::Fail,
        },
        Some(PropertyKind::Data) => match data_pair(triples, index) {
            Some((left, right)) => {
                Read::Found(Axiom::DisjointDataProperties(two(left, right)), state)
            }
            None => Read::Fail,
        },
        _ => Read::Fail,
    }
}

fn inverse_properties(triples: &Vec<Triple>, index: usize, state: State) -> Read {
    match &triples[index].subject {
        Subject::Iri(_) => {
            let state = take(state, index);
            match property_pair(triples, index, state) {
                Some((left, right, state)) => {
                    Read::Found(Axiom::InverseObjectProperties(left, right), state)
                }
                None => Read::Fail,
            }
        }
        Subject::Blank(_) => Read::Skip(state),
    }
}

/// The domain or range axiom of the main triple: `range` selects range.
fn domain_range(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    range: bool,
    fuel: usize,
) -> Read {
    let state = take(state, index);
    let subject = subject_node(&triples[index].subject);
    match node_kind(kinds, &subject) {
        Some(PropertyKind::Object) => match property_expression(triples, &subject, state) {
            Some((role, state)) => {
                match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                    Some((filler, state)) => {
                        if range {
                            Read::Found(Axiom::ObjectPropertyRange(role, filler), state)
                        } else {
                            Read::Found(Axiom::ObjectPropertyDomain(role, filler), state)
                        }
                    }
                    None => Read::Fail,
                }
            }
            None => Read::Fail,
        },
        Some(PropertyKind::Data) => match node_iri(&subject) {
            Some(iri) => {
                if range {
                    match data_range(triples, kinds, &triples[index].object, state, fuel) {
                        Some((filler, state)) => Read::Found(
                            Axiom::DataPropertyRange(DataProperty { iri }, filler),
                            state,
                        ),
                        None => Read::Fail,
                    }
                } else {
                    match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                        Some((filler, state)) => Read::Found(
                            Axiom::DataPropertyDomain(DataProperty { iri }, filler),
                            state,
                        ),
                        None => Read::Fail,
                    }
                }
            }
            None => Read::Fail,
        },
        Some(PropertyKind::Annotation) => match node_iri(&subject) {
            Some(iri) => match node_iri(&triples[index].object) {
                Some(target) => {
                    if range {
                        Read::Found(
                            Axiom::AnnotationPropertyRange(AnnotationProperty { iri }, target),
                            state,
                        )
                    } else {
                        Read::Found(
                            Axiom::AnnotationPropertyDomain(AnnotationProperty { iri }, target),
                            state,
                        )
                    }
                }
                None => Read::Fail,
            },
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

/// The individuals of the subject and object of the main triple.
fn individual_pair(triples: &Vec<Triple>, index: usize) -> Option<(Individual, Individual)> {
    match node_individual(&subject_node(&triples[index].subject)) {
        Some(left) => match node_individual(&triples[index].object) {
            Some(right) => Some((left, right)),
            None => None,
        },
        None => None,
    }
}

fn same_individual(triples: &Vec<Triple>, index: usize, state: State) -> Read {
    match individual_pair(triples, index) {
        Some((left, right)) => {
            Read::Found(Axiom::SameIndividual(two(left, right)), take(state, index))
        }
        None => Read::Fail,
    }
}

fn different_individuals(triples: &Vec<Triple>, index: usize, state: State) -> Read {
    match individual_pair(triples, index) {
        Some((left, right)) => Read::Found(
            Axiom::DifferentIndividuals(two(left, right)),
            take(state, index),
        ),
        None => Read::Fail,
    }
}

fn has_key(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State, fuel: usize) -> Read {
    let state = take(state, index);
    let subject = subject_node(&triples[index].subject);
    match class_expression(triples, kinds, &subject, state, fuel) {
        Some((class, state)) => {
            match cells(triples, &triples[index].object, state, Vec::new(), fuel) {
                Some((firsts, state)) => {
                    match key_members(triples, kinds, &firsts, 0, state, Vec::new(), Vec::new()) {
                        Some((objects, datas, state)) => {
                            Read::Found(Axiom::HasKey(class, objects, datas), state)
                        }
                        None => Read::Fail,
                    }
                }
                None => Read::Fail,
            }
        }
        None => Read::Fail,
    }
}

/// A property characteristic of the subject of the main triple: `kind`
/// numbers functional, inverse functional, reflexive, irreflexive, symmetric,
/// asymmetric and transitive from 0.
fn characteristic(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    kind: u8,
) -> Read {
    let state = take(state, index);
    let subject = subject_node(&triples[index].subject);
    match node_kind(kinds, &subject) {
        Some(PropertyKind::Object) => match property_expression(triples, &subject, state) {
            Some((role, state)) => {
                if kind == 0 {
                    Read::Found(Axiom::FunctionalObjectProperty(role), state)
                } else if kind == 1 {
                    Read::Found(Axiom::InverseFunctionalObjectProperty(role), state)
                } else if kind == 2 {
                    Read::Found(Axiom::ReflexiveObjectProperty(role), state)
                } else if kind == 3 {
                    Read::Found(Axiom::IrreflexiveObjectProperty(role), state)
                } else if kind == 4 {
                    Read::Found(Axiom::SymmetricObjectProperty(role), state)
                } else if kind == 5 {
                    Read::Found(Axiom::AsymmetricObjectProperty(role), state)
                } else {
                    Read::Found(Axiom::TransitiveObjectProperty(role), state)
                }
            }
            None => Read::Fail,
        },
        Some(PropertyKind::Data) => {
            if kind == 0 {
                match node_iri(&subject) {
                    Some(iri) => {
                        Read::Found(Axiom::FunctionalDataProperty(DataProperty { iri }), state)
                    }
                    None => Read::Fail,
                }
            } else {
                Read::Fail
            }
        }
        _ => Read::Fail,
    }
}

/// The blank axiom node of the main triple, recorded.
fn axiom_node(triples: &Vec<Triple>, index: usize, state: State) -> Option<(BlankNode, State)> {
    match &triples[index].subject {
        Subject::Blank(blank) => {
            let state = take(state, index);
            let state = record(state, blank);
            Some((copy_blank(blank), state))
        }
        Subject::Iri(_) => None,
    }
}

fn all_disjoint_classes(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    match axiom_node(triples, index, state) {
        Some((blank, state)) => match find(
            triples,
            &state,
            &blank,
            b"http://www.w3.org/2002/07/owl#members",
        ) {
            Some(list) => {
                let state = take(state, list);
                match class_list2(triples, kinds, &triples[list].object, state, fuel) {
                    Some((members, state)) => {
                        if members.rest.len() >= 1 {
                            Read::Found(Axiom::DisjointClasses(members), state)
                        } else {
                            Read::Fail
                        }
                    }
                    None => Read::Fail,
                }
            }
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

/// The kind of the first member of the list a node starts.
fn first_member_kind(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    state: &State,
    node: &Object,
) -> Option<PropertyKind> {
    match node {
        Object::Blank(blank) => match find(
            triples,
            state,
            blank,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#first",
        ) {
            Some(first) => node_kind(kinds, &triples[first].object),
            None => None,
        },
        _ => None,
    }
}

fn all_disjoint_properties(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    match axiom_node(triples, index, state) {
        Some((blank, state)) => match find(
            triples,
            &state,
            &blank,
            b"http://www.w3.org/2002/07/owl#members",
        ) {
            Some(list) => {
                let state = take(state, list);
                match first_member_kind(triples, kinds, &state, &triples[list].object) {
                    Some(PropertyKind::Object) => {
                        match property_list2(triples, kinds, &triples[list].object, state, fuel) {
                            Some((members, state)) => {
                                if members.rest.len() >= 1 {
                                    Read::Found(Axiom::DisjointObjectProperties(members), state)
                                } else {
                                    Read::Fail
                                }
                            }
                            None => Read::Fail,
                        }
                    }
                    Some(PropertyKind::Data) => {
                        match data_list2(triples, kinds, &triples[list].object, state, fuel) {
                            Some((members, state)) => {
                                if members.rest.len() >= 1 {
                                    Read::Found(Axiom::DisjointDataProperties(members), state)
                                } else {
                                    Read::Fail
                                }
                            }
                            None => Read::Fail,
                        }
                    }
                    _ => Read::Fail,
                }
            }
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

fn all_different(triples: &Vec<Triple>, index: usize, state: State, fuel: usize) -> Read {
    match axiom_node(triples, index, state) {
        Some((blank, state)) => match find(
            triples,
            &state,
            &blank,
            b"http://www.w3.org/2002/07/owl#members",
        ) {
            Some(list) => {
                let state = take(state, list);
                match individual_list2(triples, &triples[list].object, state, fuel) {
                    Some((members, state)) => {
                        if members.rest.len() >= 1 {
                            Read::Found(Axiom::DifferentIndividuals(members), state)
                        } else {
                            Read::Fail
                        }
                    }
                    None => Read::Fail,
                }
            }
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

fn negative_assertion(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State) -> Read {
    match axiom_node(triples, index, state) {
        Some((blank, state)) => match find(
            triples,
            &state,
            &blank,
            b"http://www.w3.org/2002/07/owl#sourceIndividual",
        ) {
            Some(source) => match node_individual(&triples[source].object) {
                Some(subject) => {
                    let state = take(state, source);
                    match find(
                        triples,
                        &state,
                        &blank,
                        b"http://www.w3.org/2002/07/owl#assertionProperty",
                    ) {
                        Some(property) => {
                            let state = take(state, property);
                            let node = &triples[property].object;
                            match node_kind(kinds, node) {
                                Some(PropertyKind::Object) => {
                                    match property_expression(triples, node, state) {
                                        Some((role, state)) => match find(
                                            triples,
                                            &state,
                                            &blank,
                                            b"http://www.w3.org/2002/07/owl#targetIndividual",
                                        ) {
                                            Some(target) => {
                                                match node_individual(&triples[target].object) {
                                                    Some(object) => Read::Found(
                                                        Axiom::NegativeObjectPropertyAssertion(
                                                            role, subject, object,
                                                        ),
                                                        take(state, target),
                                                    ),
                                                    None => Read::Fail,
                                                }
                                            }
                                            None => Read::Fail,
                                        },
                                        None => Read::Fail,
                                    }
                                }
                                Some(PropertyKind::Data) => match node_iri(node) {
                                    Some(iri) => match find(
                                        triples,
                                        &state,
                                        &blank,
                                        b"http://www.w3.org/2002/07/owl#targetValue",
                                    ) {
                                        Some(target) => match node_literal(&triples[target].object)
                                        {
                                            Some(value) => Read::Found(
                                                Axiom::NegativeDataPropertyAssertion(
                                                    DataProperty { iri },
                                                    subject,
                                                    value,
                                                ),
                                                take(state, target),
                                            ),
                                            None => Read::Fail,
                                        },
                                        None => Read::Fail,
                                    },
                                    None => Read::Fail,
                                },
                                _ => Read::Fail,
                            }
                        }
                        None => Read::Fail,
                    }
                }
                None => Read::Fail,
            },
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

fn class_assertion(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    let state = take(state, index);
    match node_individual(&subject_node(&triples[index].subject)) {
        Some(individual) => {
            match class_expression(triples, kinds, &triples[index].object, state, fuel) {
                Some((class, state)) => {
                    Read::Found(Axiom::ClassAssertion(class, individual), state)
                }
                None => Read::Fail,
            }
        }
        None => Read::Fail,
    }
}

/// Whether the triple's subject is a blank node.
fn blank_subject(triple: &Triple) -> bool {
    match &triple.subject {
        Subject::Blank(_) => true,
        Subject::Iri(_) => false,
    }
}

/// The `rdf:type` main triple at `index`.
fn typing(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State, fuel: usize) -> Read {
    let object = &triples[index].object;
    if object_is(object, b"http://www.w3.org/2002/07/owl#Restriction") {
        if blank_subject(&triples[index]) {
            Read::Skip(state)
        } else {
            Read::Fail
        }
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#Class") {
        if blank_subject(&triples[index]) {
            Read::Skip(state)
        } else {
            Read::Fail
        }
    } else if object_is(object, b"http://www.w3.org/2000/01/rdf-schema#Datatype") {
        if blank_subject(&triples[index]) {
            Read::Skip(state)
        } else {
            Read::Fail
        }
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#FunctionalProperty") {
        characteristic(triples, kinds, index, state, 0)
    } else if object_is(
        object,
        b"http://www.w3.org/2002/07/owl#InverseFunctionalProperty",
    ) {
        characteristic(triples, kinds, index, state, 1)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#ReflexiveProperty") {
        characteristic(triples, kinds, index, state, 2)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#IrreflexiveProperty") {
        characteristic(triples, kinds, index, state, 3)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#SymmetricProperty") {
        characteristic(triples, kinds, index, state, 4)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#AsymmetricProperty") {
        characteristic(triples, kinds, index, state, 5)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#TransitiveProperty") {
        characteristic(triples, kinds, index, state, 6)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#AllDisjointClasses") {
        all_disjoint_classes(triples, kinds, index, state, fuel)
    } else if object_is(
        object,
        b"http://www.w3.org/2002/07/owl#AllDisjointProperties",
    ) {
        all_disjoint_properties(triples, kinds, index, state, fuel)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#AllDifferent") {
        all_different(triples, index, state, fuel)
    } else if object_is(
        object,
        b"http://www.w3.org/2002/07/owl#NegativePropertyAssertion",
    ) {
        negative_assertion(triples, kinds, index, state)
    } else if reserved_object(object) {
        Read::Fail
    } else {
        class_assertion(triples, kinds, index, state, fuel)
    }
}

/// Whether the node is an IRI of the RDF, RDFS, OWL or XSD vocabulary that no
/// class assertion names: everything reserved except `owl:Thing` and
/// `owl:Nothing`.
fn reserved_object(node: &Object) -> bool {
    match node {
        Object::Iri(iri) => {
            if crate::vocabulary::reserved_iri(&iri.spelling) {
                if same(&iri.spelling, b"http://www.w3.org/2002/07/owl#Thing") {
                    false
                } else {
                    !same(&iri.spelling, b"http://www.w3.org/2002/07/owl#Nothing")
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// An assertion along a declared or built-in property.
fn assertion(triples: &Vec<Triple>, kinds: &Kinds, index: usize, state: State) -> Read {
    let triple = &triples[index];
    match property_kind(kinds, &triple.predicate.spelling) {
        Some(PropertyKind::Object) => match individual_pair(triples, index) {
            Some((subject, object)) => Read::Found(
                Axiom::ObjectPropertyAssertion(
                    ObjectPropertyExpression::Property(ObjectProperty {
                        iri: iri_of(&triple.predicate.spelling),
                    }),
                    subject,
                    object,
                ),
                take(state, index),
            ),
            None => Read::Fail,
        },
        Some(PropertyKind::Data) => match node_individual(&subject_node(&triple.subject)) {
            Some(subject) => match node_literal(&triple.object) {
                Some(value) => Read::Found(
                    Axiom::DataPropertyAssertion(
                        DataProperty {
                            iri: iri_of(&triple.predicate.spelling),
                        },
                        subject,
                        value,
                    ),
                    take(state, index),
                ),
                None => Read::Fail,
            },
            None => Read::Fail,
        },
        Some(PropertyKind::Annotation) => match annotation_value(&triple.object) {
            Some(value) => Read::Found(
                Axiom::AnnotationAssertion(
                    AnnotationProperty {
                        iri: iri_of(&triple.predicate.spelling),
                    },
                    annotation_subject(&triple.subject),
                    value,
                ),
                take(state, index),
            ),
            None => Read::Fail,
        },
        None => Read::Fail,
    }
}

fn annotation_subject(subject: &Subject) -> AnnotationSubject {
    match subject {
        Subject::Iri(iri) => AnnotationSubject::Iri(iri_of(&iri.spelling)),
        Subject::Blank(blank) => AnnotationSubject::Anonymous(AnonymousIndividual {
            scope: copy_bytes(&blank.scope),
            label: copy_bytes(&blank.label),
        }),
    }
}

fn annotation_value(node: &Object) -> Option<AnnotationValue> {
    match node {
        Object::Iri(iri) => Some(AnnotationValue::Iri(iri_of(&iri.spelling))),
        Object::Blank(blank) => Some(AnnotationValue::Anonymous(AnonymousIndividual {
            scope: copy_bytes(&blank.scope),
            label: copy_bytes(&blank.label),
        })),
        Object::Literal(literal) => match literal_of(literal) {
            Some(value) => Some(AnnotationValue::Literal(value)),
            None => None,
        },
    }
}

/// Whether a predicate is reserved vocabulary that names no property.
fn structural(name: &Vec<u8>) -> bool {
    if crate::vocabulary::reserved_iri(name) {
        match builtin_kind(name) {
            Some(EntityKind::ObjectProperty) => false,
            Some(EntityKind::DataProperty) => false,
            Some(EntityKind::AnnotationProperty) => false,
            _ => true,
        }
    } else {
        false
    }
}

/// What the unused triple at `index` starts.
fn read_axiom(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    fuel: usize,
) -> Read {
    let name = &triples[index].predicate.spelling;
    if same(name, b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type") {
        typing(triples, kinds, index, state, fuel)
    } else if same(name, b"http://www.w3.org/2000/01/rdf-schema#subClassOf") {
        sub_class(triples, kinds, index, state, fuel)
    } else if same(name, b"http://www.w3.org/2002/07/owl#equivalentClass") {
        equivalent_class(triples, kinds, index, state, fuel)
    } else if same(name, b"http://www.w3.org/2002/07/owl#disjointWith") {
        disjoint_class(triples, kinds, index, state, fuel)
    } else if same(name, b"http://www.w3.org/2002/07/owl#disjointUnionOf") {
        disjoint_union(triples, kinds, index, state, fuel)
    } else if same(name, b"http://www.w3.org/2000/01/rdf-schema#subPropertyOf") {
        sub_property(triples, kinds, index, state)
    } else if same(name, b"http://www.w3.org/2002/07/owl#propertyChainAxiom") {
        property_chain(triples, kinds, index, state, fuel)
    } else if same(name, b"http://www.w3.org/2002/07/owl#equivalentProperty") {
        equivalent_property(triples, kinds, index, state)
    } else if same(name, b"http://www.w3.org/2002/07/owl#propertyDisjointWith") {
        disjoint_property(triples, kinds, index, state)
    } else if same(name, b"http://www.w3.org/2002/07/owl#inverseOf") {
        inverse_properties(triples, index, state)
    } else if same(name, b"http://www.w3.org/2000/01/rdf-schema#domain") {
        domain_range(triples, kinds, index, state, false, fuel)
    } else if same(name, b"http://www.w3.org/2000/01/rdf-schema#range") {
        domain_range(triples, kinds, index, state, true, fuel)
    } else if same(name, b"http://www.w3.org/2002/07/owl#sameAs") {
        same_individual(triples, index, state)
    } else if same(name, b"http://www.w3.org/2002/07/owl#differentFrom") {
        different_individuals(triples, index, state)
    } else if same(name, b"http://www.w3.org/2002/07/owl#hasKey") {
        has_key(triples, kinds, index, state, fuel)
    } else if structural(name) {
        Read::Skip(state)
    } else {
        assertion(triples, kinds, index, state)
    }
}

/// `out` followed by the axioms that the unused triples of `triples[index..]`
/// start.
fn axioms_from(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    index: usize,
    state: State,
    mut out: Vec<AnnotatedAxiom>,
) -> Option<(Vec<AnnotatedAxiom>, State)> {
    if index < triples.len() {
        if is_used(&state.used, index) {
            axioms_from(triples, kinds, index + 1, state, out)
        } else {
            match read_axiom(triples, kinds, index, state, triples.len()) {
                Read::Skip(state) => axioms_from(triples, kinds, index + 1, state, out),
                Read::Found(axiom, state) => {
                    if out.len() < usize::MAX {
                        out.push(AnnotatedAxiom {
                            annotations: Vec::new(),
                            axiom,
                        });
                        axioms_from(triples, kinds, index + 1, state, out)
                    } else {
                        None
                    }
                }
                Read::Fail => None,
            }
        }
    } else {
        Some((out, state))
    }
}

/// The kind a declaration triple's object declares.
fn declaration_kind(object: &Object) -> Option<EntityKind> {
    if object_is(object, b"http://www.w3.org/2002/07/owl#Class") {
        Some(EntityKind::Class)
    } else if object_is(object, b"http://www.w3.org/2000/01/rdf-schema#Datatype") {
        Some(EntityKind::Datatype)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#ObjectProperty") {
        Some(EntityKind::ObjectProperty)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#DatatypeProperty") {
        Some(EntityKind::DataProperty)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#AnnotationProperty") {
        Some(EntityKind::AnnotationProperty)
    } else if object_is(object, b"http://www.w3.org/2002/07/owl#NamedIndividual") {
        Some(EntityKind::NamedIndividual)
    } else {
        None
    }
}

fn entity_of(kind: &EntityKind, spelling: &Vec<u8>) -> Entity {
    let iri = iri_of(spelling);
    match kind {
        EntityKind::Class => Entity::Class(Class { iri }),
        EntityKind::Datatype => Entity::Datatype(Datatype { iri }),
        EntityKind::ObjectProperty => Entity::ObjectProperty(ObjectProperty { iri }),
        EntityKind::DataProperty => Entity::DataProperty(DataProperty { iri }),
        EntityKind::AnnotationProperty => Entity::AnnotationProperty(AnnotationProperty { iri }),
        EntityKind::NamedIndividual => Entity::NamedIndividual(NamedIndividual { iri }),
    }
}

/// The declarations with the IRI declared with the kind, in the bucket of the IRI.
fn add_kind(mut kinds: Kinds, iri: Vec<u8>, kind: EntityKind) -> Option<Kinds> {
    let bucket = bucket_of(hash_iri(&iri), kinds.buckets.len());
    if bucket < kinds.buckets.len() {
        if kinds.buckets[bucket].len() < usize::MAX {
            kinds.buckets[bucket].push(Declared { iri, kind });
            Some(kinds)
        } else {
            None
        }
    } else {
        None
    }
}

/// The declarations of `triples[index..]`, after `axioms` and `kinds`, used.
fn declarations(
    triples: &Vec<Triple>,
    index: usize,
    state: State,
    mut axioms: Vec<AnnotatedAxiom>,
    kinds: Kinds,
) -> Option<(Vec<AnnotatedAxiom>, Kinds, State)> {
    if index < triples.len() {
        let triple = &triples[index];
        let declared = if same(
            &triple.predicate.spelling,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
        ) {
            match &triple.subject {
                Subject::Iri(iri) => match declaration_kind(&triple.object) {
                    Some(kind) => Some((copy_bytes(&iri.spelling), kind)),
                    None => None,
                },
                Subject::Blank(_) => None,
            }
        } else {
            None
        };
        match declared {
            Some((spelling, kind)) => {
                if axioms.len() < usize::MAX {
                    axioms.push(AnnotatedAxiom {
                        annotations: Vec::new(),
                        axiom: Axiom::Declaration(entity_of(&kind, &spelling)),
                    });
                    match add_kind(kinds, spelling, kind) {
                        Some(kinds) => {
                            declarations(triples, index + 1, take(state, index), axioms, kinds)
                        }
                        None => None,
                    }
                } else {
                    None
                }
            }
            None => declarations(triples, index + 1, state, axioms, kinds),
        }
    } else {
        Some((axioms, kinds, state))
    }
}

/// The first unused triple of `triples[index..]` typing an IRI as `owl:Ontology`.
fn find_header(triples: &Vec<Triple>, used: &Vec<bool>, index: usize) -> Option<usize> {
    if index < triples.len() {
        if is_used(used, index) {
            find_header(triples, used, index + 1)
        } else if same(
            &triples[index].predicate.spelling,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
        ) {
            if object_is(
                &triples[index].object,
                b"http://www.w3.org/2002/07/owl#Ontology",
            ) {
                match &triples[index].subject {
                    Subject::Iri(_) => Some(index),
                    Subject::Blank(_) => find_header(triples, used, index + 1),
                }
            } else {
                find_header(triples, used, index + 1)
            }
        } else {
            find_header(triples, used, index + 1)
        }
    } else {
        None
    }
}

/// Whether the triple's subject is the IRI.
fn about_iri(triple: &Triple, spelling: &Vec<u8>) -> bool {
    match &triple.subject {
        Subject::Iri(iri) => same_vec(&iri.spelling, spelling),
        Subject::Blank(_) => false,
    }
}

/// The header triples of `triples[index..]` about the ontology IRI: the version
/// IRI, the imports and the annotations, after the given ones, used.
fn header_parts(
    triples: &Vec<Triple>,
    kinds: &Kinds,
    ontology: &Vec<u8>,
    index: usize,
    state: State,
    mut version: Option<Iri>,
    mut imports: Vec<Iri>,
    mut annotations: Vec<Annotation>,
) -> Option<(Option<Iri>, Vec<Iri>, Vec<Annotation>, State)> {
    if index < triples.len() {
        if is_used(&state.used, index) {
            header_parts(
                triples,
                kinds,
                ontology,
                index + 1,
                state,
                version,
                imports,
                annotations,
            )
        } else if about_iri(&triples[index], ontology) {
            let name = &triples[index].predicate.spelling;
            if same(name, b"http://www.w3.org/2002/07/owl#versionIRI") {
                match version {
                    Some(_) => None,
                    None => match node_iri(&triples[index].object) {
                        Some(iri) => {
                            version = Some(iri);
                            header_parts(
                                triples,
                                kinds,
                                ontology,
                                index + 1,
                                take(state, index),
                                version,
                                imports,
                                annotations,
                            )
                        }
                        None => None,
                    },
                }
            } else if same(name, b"http://www.w3.org/2002/07/owl#imports") {
                match node_iri(&triples[index].object) {
                    Some(iri) => {
                        if imports.len() < usize::MAX {
                            imports.push(iri);
                            header_parts(
                                triples,
                                kinds,
                                ontology,
                                index + 1,
                                take(state, index),
                                version,
                                imports,
                                annotations,
                            )
                        } else {
                            None
                        }
                    }
                    None => None,
                }
            } else {
                match property_kind(kinds, name) {
                    Some(PropertyKind::Annotation) => {
                        match annotation_value(&triples[index].object) {
                            Some(value) => {
                                if annotations.len() < usize::MAX {
                                    annotations.push(Annotation {
                                        annotations: Vec::new(),
                                        property: AnnotationProperty { iri: iri_of(name) },
                                        value,
                                    });
                                    header_parts(
                                        triples,
                                        kinds,
                                        ontology,
                                        index + 1,
                                        take(state, index),
                                        version,
                                        imports,
                                        annotations,
                                    )
                                } else {
                                    None
                                }
                            }
                            None => None,
                        }
                    }
                    _ => header_parts(
                        triples,
                        kinds,
                        ontology,
                        index + 1,
                        state,
                        version,
                        imports,
                        annotations,
                    ),
                }
            }
        } else {
            header_parts(
                triples,
                kinds,
                ontology,
                index + 1,
                state,
                version,
                imports,
                annotations,
            )
        }
    } else {
        Some((version, imports, annotations, state))
    }
}

/// Whether an equal triple of `triples[index..]` is used.
fn repeats_used(triples: &Vec<Triple>, used: &Vec<bool>, triple: &Triple, index: usize) -> bool {
    if index < triples.len() {
        if is_used(used, index) {
            if same_triple(&triples[index], triple) {
                true
            } else {
                repeats_used(triples, used, triple, index + 1)
            }
        } else {
            repeats_used(triples, used, triple, index + 1)
        }
    } else {
        false
    }
}

/// Whether every triple of `triples[index..]` is used or repeats a used one.
fn all_read(triples: &Vec<Triple>, used: &Vec<bool>, index: usize) -> bool {
    if index < triples.len() {
        if is_used(used, index) {
            all_read(triples, used, index + 1)
        } else if repeats_used(triples, used, &triples[index], 0) {
            all_read(triples, used, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

fn unused(count: usize, mut out: Vec<bool>) -> Vec<bool> {
    if out.len() < count {
        out.push(false);
        unused(count, out)
    } else {
        out
    }
}

/// The ontology a graph is the forward mapping of, with the blank nodes that
/// mapping allocates; `None` when the graph is no such image or an entity's
/// type is missing or ambiguous.
pub fn map_graph(graph: &RawGraph) -> Option<Mapped> {
    let triples = &graph.triples;
    let count = bucket_count(triples.len());
    let state = State {
        used: unused(triples.len(), Vec::new()),
        blanks: Vec::new(),
        subjects: subjects_from(triples, 0, empty_buckets(count, Vec::new())),
    };
    let kinds = Kinds {
        buckets: empty_buckets(count, Vec::new()),
    };
    match declarations(triples, 0, state, Vec::new(), kinds) {
        Some((axioms, kinds, state)) => {
            let (identity, imports, annotations, state) = match find_header(triples, &state.used, 0)
            {
                Some(header) => match &triples[header].subject {
                    Subject::Iri(iri) => {
                        let state = take(state, header);
                        match header_parts(
                            triples,
                            &kinds,
                            &iri.spelling,
                            0,
                            state,
                            None,
                            Vec::new(),
                            Vec::new(),
                        ) {
                            Some((version, imports, annotations, state)) => (
                                OntologyIdentity::Named {
                                    ontology: iri_of(&iri.spelling),
                                    version,
                                },
                                imports,
                                annotations,
                                state,
                            ),
                            None => return None,
                        }
                    }
                    Subject::Blank(_) => return None,
                },
                None => (OntologyIdentity::Anonymous, Vec::new(), Vec::new(), state),
            };
            match axioms_from(triples, &kinds, 0, state, axioms) {
                Some((axioms, state)) => {
                    if all_read(triples, &state.used, 0) {
                        Some(Mapped {
                            ontology: RawOntology {
                                identity,
                                imports,
                                annotations,
                                axioms,
                            },
                            blanks: state.blanks,
                        })
                    } else {
                        None
                    }
                }
                None => None,
            }
        }
        None => None,
    }
}
