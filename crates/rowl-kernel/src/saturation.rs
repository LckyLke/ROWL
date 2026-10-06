//! Classification of ontologies in the EL fragment by saturation.
//!
//! The logical axioms must be EL: subclass, equivalence and disjointness axioms
//! between class expressions built from named classes, `owl:Thing`,
//! `owl:Nothing`, intersections and existential restrictions on named object
//! properties; object property domains; inclusions and equivalences of named
//! object properties, chains of two of them and transitivity. Declarations and
//! annotation axioms are ignored; any other axiom makes `classify` decline
//! with `None`, as does a limit of the machine.
//!
//! Every class expression of the axioms is interned into a table of concepts
//! whose parts come before them. Saturation derives, for every context (a
//! concept whose subsumers are needed), the concepts that subsume it, and links
//! `x r y` meaning that every instance of `x` has an `r`-successor in `y`, until
//! no rule adds anything. A final pass checks that the result is closed under
//! every rule, and the answers are read from it: a class is unsatisfiable when
//! `owl:Nothing` subsumes it, and subsumed by the classes it lists.
//!
//! The scans over lists that grow while they run stop at the length the list
//! had when the scan started; whatever they leave is found by the processing
//! of the later facts, and the final check confirms that nothing is missing.
#![allow(
    clippy::ptr_arg,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::len_zero,
    clippy::too_many_arguments,
    clippy::needless_return,
    clippy::question_mark,
    clippy::manual_map,
    clippy::new_without_default,
    clippy::match_like_matches_macro,
    clippy::collapsible_match,
    clippy::vec_init_then_push,
    clippy::type_complexity
)]

use crate::alc_ontology::same_pattern;
use crate::classification::Classification;
use crate::model::{
    AnnotatedAxiom, Axiom, Class, ClassExpression, ObjectProperty, ObjectPropertyExpression,
    SubObjectPropertyExpression,
};
use crate::nnf::copy_iri;
use crate::symbols::same_spelling;

/// The number of hash buckets of the concept table.
const BUCKETS: usize = 4096;

/// A concept of the table; the parts of a compound concept are earlier
/// concepts of the table, and a role is an index into the role list.
pub enum Concept {
    Top,
    Bottom,
    Atom(Class),
    And(usize, usize),
    Exists(usize, usize),
}

/// The concepts, interned by hash bucket, and the named object properties.
pub struct Table {
    pub concepts: Vec<Concept>,
    pub buckets: Vec<Vec<usize>>,
    pub roles: Vec<ObjectProperty>,
}

/// An axiom of the EL fragment over the table.
pub enum Rule {
    /// The first concept is subsumed by the second.
    Sub(usize, usize),
    /// The first role is included in the second.
    Role(usize, usize),
    /// The chain of the first two roles is included in the third.
    Chain(usize, usize, usize),
}

/// The axioms indexed for saturation.
pub struct Rules {
    pub top: usize,
    pub bottom: usize,
    /// For every concept, the concepts that subsume it by an axiom.
    pub told: Vec<Vec<usize>>,
    /// For every concept, the other parts and the conjunctions it is part of on
    /// the left of an axiom.
    pub conjunctions: Vec<Vec<(usize, usize)>>,
    /// For every concept, the roles and existential restrictions it is the
    /// filler of on the left of an axiom.
    pub existentials: Vec<Vec<(usize, usize)>>,
    /// For every role, the roles that include it.
    pub supers: Vec<Vec<usize>>,
    /// For every role, the second roles and the results of the chains it starts.
    pub firsts: Vec<Vec<(usize, usize)>>,
    /// For every role, the first roles and the results of the chains it ends.
    pub seconds: Vec<Vec<(usize, usize)>>,
}

/// A derived fact still to be processed.
pub enum Fact {
    /// The second concept subsumes the first context.
    Sub(usize, usize),
    /// Every instance of the first context has a successor along the role in
    /// the third.
    Link(usize, usize, usize),
}

/// The derived subsumers and links, and the facts still to be processed.
pub struct State {
    pub subsumers: Vec<Vec<usize>>,
    pub active: Vec<bool>,
    pub out: Vec<Vec<(usize, usize)>>,
    pub into: Vec<Vec<(usize, usize)>>,
    pub queue: Vec<Fact>,
    pub next: usize,
}

fn is_thing(class: &Class) -> bool {
    same_pattern(&class.iri.spelling, b"http://www.w3.org/2002/07/owl#Thing")
}
fn is_nothing(class: &Class) -> bool {
    same_pattern(
        &class.iri.spelling,
        b"http://www.w3.org/2002/07/owl#Nothing",
    )
}
fn builtin_role(role: &ObjectProperty) -> bool {
    if same_pattern(
        &role.iri.spelling,
        b"http://www.w3.org/2002/07/owl#topObjectProperty",
    ) {
        true
    } else {
        same_pattern(
            &role.iri.spelling,
            b"http://www.w3.org/2002/07/owl#bottomObjectProperty",
        )
    }
}

fn copy_class(class: &Class) -> Class {
    Class {
        iri: copy_iri(&class.iri),
    }
}
fn copy_role(role: &ObjectProperty) -> ObjectProperty {
    ObjectProperty {
        iri: copy_iri(&role.iri),
    }
}

/// `(hash * 31 + value) mod BUCKETS`, without overflow.
fn mix(hash: usize, value: usize) -> usize {
    ((hash % BUCKETS) * 31 + value % BUCKETS) % BUCKETS
}
fn hash_from(bytes: &Vec<u8>, index: usize, hash: usize) -> usize {
    if index < bytes.len() {
        hash_from(bytes, index + 1, mix(hash, bytes[index] as usize))
    } else {
        hash
    }
}
fn hash_concept(concept: &Concept) -> usize {
    match concept {
        Concept::Top => 1,
        Concept::Bottom => 2,
        Concept::Atom(class) => hash_from(&class.iri.spelling, 0, 7),
        Concept::And(left, right) => mix(mix(3, *left), *right),
        Concept::Exists(role, filler) => mix(mix(5, *role), *filler),
    }
}

fn same_concept(left: &Concept, right: &Concept) -> bool {
    match left {
        Concept::Top => match right {
            Concept::Top => true,
            _ => false,
        },
        Concept::Bottom => match right {
            Concept::Bottom => true,
            _ => false,
        },
        Concept::Atom(a) => match right {
            Concept::Atom(b) => same_spelling(&a.iri.spelling, &b.iri.spelling),
            _ => false,
        },
        Concept::And(a, b) => match right {
            Concept::And(c, d) => {
                if *a == *c {
                    *b == *d
                } else {
                    false
                }
            }
            _ => false,
        },
        Concept::Exists(r, f) => match right {
            Concept::Exists(s, g) => {
                if *r == *s {
                    *f == *g
                } else {
                    false
                }
            }
            _ => false,
        },
    }
}

/// A concept of `bucket[index..]` equal to `concept`, if any.
fn find_from(
    concepts: &Vec<Concept>,
    bucket: &Vec<usize>,
    concept: &Concept,
    index: usize,
) -> Option<usize> {
    if index < bucket.len() {
        let id = bucket[index];
        if id < concepts.len() {
            if same_concept(&concepts[id], concept) {
                return Some(id);
            }
        }
        find_from(concepts, bucket, concept, index + 1)
    } else {
        None
    }
}

fn empty_buckets(mut out: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    if out.len() < BUCKETS {
        out.push(Vec::new());
        empty_buckets(out)
    } else {
        out
    }
}

/// An empty table.
pub fn empty_table() -> Table {
    Table {
        concepts: Vec::new(),
        buckets: empty_buckets(Vec::new()),
        roles: Vec::new(),
    }
}

/// The index of `concept` in the table, added when it is new.
pub fn intern(mut table: Table, concept: Concept) -> Option<(Table, usize)> {
    let hash = hash_concept(&concept);
    if hash < table.buckets.len() {
        match find_from(&table.concepts, &table.buckets[hash], &concept, 0) {
            Some(id) => Some((table, id)),
            None => {
                let id = table.concepts.len();
                if id < usize::MAX {
                    if table.buckets[hash].len() < usize::MAX {
                        table.concepts.push(concept);
                        table.buckets[hash].push(id);
                        Some((table, id))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
    } else {
        None
    }
}

fn role_from(roles: &Vec<ObjectProperty>, role: &ObjectProperty, index: usize) -> Option<usize> {
    if index < roles.len() {
        if same_spelling(&roles[index].iri.spelling, &role.iri.spelling) {
            Some(index)
        } else {
            role_from(roles, role, index + 1)
        }
    } else {
        None
    }
}

/// The index of the named object property, added when it is new.
fn intern_role(mut table: Table, role: &ObjectProperty) -> Option<(Table, usize)> {
    match role_from(&table.roles, role, 0) {
        Some(id) => Some((table, id)),
        None => {
            let id = table.roles.len();
            if id < usize::MAX {
                table.roles.push(copy_role(role));
                Some((table, id))
            } else {
                None
            }
        }
    }
}

/// The named object property of an EL role.
fn named_role(role: &ObjectPropertyExpression) -> Option<&ObjectProperty> {
    match role {
        ObjectPropertyExpression::Property(property) => {
            if builtin_role(property) {
                None
            } else {
                Some(property)
            }
        }
        ObjectPropertyExpression::Inverse(_) => None,
    }
}

/// The concept of an EL class expression.
pub fn concept_of(table: Table, expression: &ClassExpression) -> Option<(Table, usize)> {
    match expression {
        ClassExpression::Class(class) => {
            if is_thing(class) {
                intern(table, Concept::Top)
            } else if is_nothing(class) {
                intern(table, Concept::Bottom)
            } else {
                intern(table, Concept::Atom(copy_class(class)))
            }
        }
        ClassExpression::ObjectIntersectionOf(members) => {
            let (table, last) = match conjunction_of(table, &members.rest, 0) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, second) = match concept_of(table, &members.second) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, first) = match concept_of(table, &members.first) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, tail) = match last {
                Some(rest) => match intern(table, Concept::And(second, rest)) {
                    Some(pair) => pair,
                    None => return None,
                },
                None => (table, second),
            };
            intern(table, Concept::And(first, tail))
        }
        ClassExpression::ObjectSomeValuesFrom(role, filler) => {
            let property = match named_role(role) {
                Some(property) => property,
                None => return None,
            };
            let (table, inner) = match concept_of(table, filler) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, r) = match intern_role(table, property) {
                Some(pair) => pair,
                None => return None,
            };
            intern(table, Concept::Exists(r, inner))
        }
        _ => None,
    }
}

/// The right-nested conjunction of `members[index..]`, or `None` inside the
/// option when the list is exhausted.
fn conjunction_of(
    table: Table,
    members: &Vec<ClassExpression>,
    index: usize,
) -> Option<(Table, Option<usize>)> {
    if index < members.len() {
        let (table, rest) = match conjunction_of(table, members, index + 1) {
            Some(pair) => pair,
            None => return None,
        };
        let (table, head) = match concept_of(table, &members[index]) {
            Some(pair) => pair,
            None => return None,
        };
        match rest {
            Some(rest) => match intern(table, Concept::And(head, rest)) {
                Some((table, both)) => Some((table, Some(both))),
                None => None,
            },
            None => Some((table, Some(head))),
        }
    } else {
        Some((table, None))
    }
}

fn push_rule(mut rules: Vec<Rule>, rule: Rule) -> Option<Vec<Rule>> {
    if rules.len() < usize::MAX {
        rules.push(rule);
        Some(rules)
    } else {
        None
    }
}

/// The concepts of `members[index..]` added to `out`.
fn concepts_of(
    table: Table,
    members: &Vec<ClassExpression>,
    index: usize,
    mut out: Vec<usize>,
) -> Option<(Table, Vec<usize>)> {
    if index < members.len() {
        let (table, id) = match concept_of(table, &members[index]) {
            Some(pair) => pair,
            None => return None,
        };
        if out.len() < usize::MAX {
            out.push(id);
            concepts_of(table, members, index + 1, out)
        } else {
            None
        }
    } else {
        Some((table, out))
    }
}

/// The concepts of an n-ary class axiom's members, in order.
fn members_of(
    table: Table,
    first: &ClassExpression,
    second: &ClassExpression,
    rest: &Vec<ClassExpression>,
) -> Option<(Table, Vec<usize>)> {
    let (table, a) = match concept_of(table, first) {
        Some(pair) => pair,
        None => return None,
    };
    let (table, b) = match concept_of(table, second) {
        Some(pair) => pair,
        None => return None,
    };
    let mut out = Vec::new();
    out.push(a);
    out.push(b);
    concepts_of(table, rest, 0, out)
}

/// `a ⊑ b` and `b ⊑ a` for every member `a` of `members[index..]` and the next
/// member `b`: all members are then equivalent.
fn equivalences(rules: Vec<Rule>, members: &Vec<usize>, index: usize) -> Option<Vec<Rule>> {
    if index < members.len() {
        let next = index + 1;
        if next < members.len() {
            let rules = match push_rule(rules, Rule::Sub(members[index], members[next])) {
                Some(rules) => rules,
                None => return None,
            };
            let rules = match push_rule(rules, Rule::Sub(members[next], members[index])) {
                Some(rules) => rules,
                None => return None,
            };
            equivalences(rules, members, next)
        } else {
            Some(rules)
        }
    } else {
        Some(rules)
    }
}

/// `a ⊓ b ⊑ ⊥` for `a = members[index]` and every later member `b` from
/// `members[other]` on, then for the later members.
fn disjoint_pairs(
    table: Table,
    rules: Vec<Rule>,
    members: &Vec<usize>,
    bottom: usize,
    index: usize,
    other: usize,
) -> Option<(Table, Vec<Rule>)> {
    if index < members.len() {
        if other < members.len() {
            let (table, both) = match intern(table, Concept::And(members[index], members[other])) {
                Some(pair) => pair,
                None => return None,
            };
            let rules = match push_rule(rules, Rule::Sub(both, bottom)) {
                Some(rules) => rules,
                None => return None,
            };
            disjoint_pairs(table, rules, members, bottom, index, other + 1)
        } else {
            let next = index + 1;
            if next < usize::MAX {
                disjoint_pairs(table, rules, members, bottom, next, next + 1)
            } else {
                Some((table, rules))
            }
        }
    } else {
        Some((table, rules))
    }
}

/// The rules of one axiom added to `rules`, or `None` outside the EL fragment.
fn translate_axiom(
    table: Table,
    rules: Vec<Rule>,
    axiom: &Axiom,
    top: usize,
    bottom: usize,
) -> Option<(Table, Vec<Rule>)> {
    match axiom {
        Axiom::Declaration(_)
        | Axiom::AnnotationAssertion(_, _, _)
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => Some((table, rules)),
        Axiom::SubClassOf(sub, sup) => {
            let (table, a) = match concept_of(table, sub) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, b) = match concept_of(table, sup) {
                Some(pair) => pair,
                None => return None,
            };
            match push_rule(rules, Rule::Sub(a, b)) {
                Some(rules) => Some((table, rules)),
                None => None,
            }
        }
        Axiom::EquivalentClasses(members) => {
            let (table, ids) =
                match members_of(table, &members.first, &members.second, &members.rest) {
                    Some(pair) => pair,
                    None => return None,
                };
            match equivalences(rules, &ids, 0) {
                Some(rules) => Some((table, rules)),
                None => None,
            }
        }
        Axiom::DisjointClasses(members) => {
            let (table, ids) =
                match members_of(table, &members.first, &members.second, &members.rest) {
                    Some(pair) => pair,
                    None => return None,
                };
            disjoint_pairs(table, rules, &ids, bottom, 0, 1)
        }
        Axiom::ObjectPropertyDomain(role, class) => {
            let property = match named_role(role) {
                Some(property) => property,
                None => return None,
            };
            let (table, r) = match intern_role(table, property) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, some) = match intern(table, Concept::Exists(r, top)) {
                Some(pair) => pair,
                None => return None,
            };
            let (table, d) = match concept_of(table, class) {
                Some(pair) => pair,
                None => return None,
            };
            match push_rule(rules, Rule::Sub(some, d)) {
                Some(rules) => Some((table, rules)),
                None => None,
            }
        }
        Axiom::SubObjectPropertyOf(sub, sup) => {
            let property = match named_role(sup) {
                Some(property) => property,
                None => return None,
            };
            let (table, s) = match intern_role(table, property) {
                Some(pair) => pair,
                None => return None,
            };
            match sub {
                SubObjectPropertyExpression::Single(role) => {
                    let inner = match named_role(role) {
                        Some(inner) => inner,
                        None => return None,
                    };
                    let (table, r) = match intern_role(table, inner) {
                        Some(pair) => pair,
                        None => return None,
                    };
                    match push_rule(rules, Rule::Role(r, s)) {
                        Some(rules) => Some((table, rules)),
                        None => None,
                    }
                }
                SubObjectPropertyExpression::Chain(chain) => {
                    if chain.rest.len() == 0 {
                        let first = match named_role(&chain.first) {
                            Some(first) => first,
                            None => return None,
                        };
                        let second = match named_role(&chain.second) {
                            Some(second) => second,
                            None => return None,
                        };
                        let (table, r1) = match intern_role(table, first) {
                            Some(pair) => pair,
                            None => return None,
                        };
                        let (table, r2) = match intern_role(table, second) {
                            Some(pair) => pair,
                            None => return None,
                        };
                        match push_rule(rules, Rule::Chain(r1, r2, s)) {
                            Some(rules) => Some((table, rules)),
                            None => None,
                        }
                    } else {
                        None
                    }
                }
            }
        }
        Axiom::EquivalentObjectProperties(members) => {
            if members.rest.len() == 0 {
                let first = match named_role(&members.first) {
                    Some(first) => first,
                    None => return None,
                };
                let second = match named_role(&members.second) {
                    Some(second) => second,
                    None => return None,
                };
                let (table, r) = match intern_role(table, first) {
                    Some(pair) => pair,
                    None => return None,
                };
                let (table, s) = match intern_role(table, second) {
                    Some(pair) => pair,
                    None => return None,
                };
                let rules = match push_rule(rules, Rule::Role(r, s)) {
                    Some(rules) => rules,
                    None => return None,
                };
                match push_rule(rules, Rule::Role(s, r)) {
                    Some(rules) => Some((table, rules)),
                    None => None,
                }
            } else {
                None
            }
        }
        Axiom::TransitiveObjectProperty(role) => {
            let property = match named_role(role) {
                Some(property) => property,
                None => return None,
            };
            let (table, r) = match intern_role(table, property) {
                Some(pair) => pair,
                None => return None,
            };
            match push_rule(rules, Rule::Chain(r, r, r)) {
                Some(rules) => Some((table, rules)),
                None => None,
            }
        }
        _ => None,
    }
}

/// The rules of `items[index..]` added to `rules`, or `None` when an axiom is
/// outside the EL fragment.
fn translate(
    table: Table,
    rules: Vec<Rule>,
    items: &Vec<AnnotatedAxiom>,
    top: usize,
    bottom: usize,
    index: usize,
) -> Option<(Table, Vec<Rule>)> {
    if index < items.len() {
        let (table, rules) = match translate_axiom(table, rules, &items[index].axiom, top, bottom) {
            Some(pair) => pair,
            None => return None,
        };
        translate(table, rules, items, top, bottom, index + 1)
    } else {
        Some((table, rules))
    }
}

fn empty_lists(count: usize, mut out: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    if out.len() < count {
        out.push(Vec::new());
        empty_lists(count, out)
    } else {
        out
    }
}
fn empty_pairs(count: usize, mut out: Vec<Vec<(usize, usize)>>) -> Vec<Vec<(usize, usize)>> {
    if out.len() < count {
        out.push(Vec::new());
        empty_pairs(count, out)
    } else {
        out
    }
}
fn falses(count: usize, mut out: Vec<bool>) -> Vec<bool> {
    if out.len() < count {
        out.push(false);
        falses(count, out)
    } else {
        out
    }
}

fn push_pair(
    mut list: Vec<Vec<(usize, usize)>>,
    at: usize,
    pair: (usize, usize),
) -> Option<Vec<Vec<(usize, usize)>>> {
    if at < list.len() {
        if list[at].len() < usize::MAX {
            list[at].push(pair);
            Some(list)
        } else {
            None
        }
    } else {
        None
    }
}
fn push_item(mut list: Vec<Vec<usize>>, at: usize, item: usize) -> Option<Vec<Vec<usize>>> {
    if at < list.len() {
        if list[at].len() < usize::MAX {
            list[at].push(item);
            Some(list)
        } else {
            None
        }
    } else {
        None
    }
}

/// The left-hand side `c` of an axiom: register the conjunctions and
/// existential restrictions inside it, once each.
fn register(
    concepts: &Vec<Concept>,
    conjunctions: Vec<Vec<(usize, usize)>>,
    existentials: Vec<Vec<(usize, usize)>>,
    mut seen: Vec<bool>,
    c: usize,
) -> Option<(
    Vec<Vec<(usize, usize)>>,
    Vec<Vec<(usize, usize)>>,
    Vec<bool>,
)> {
    if c < concepts.len() {
        if c < seen.len() {
            if seen[c] {
                Some((conjunctions, existentials, seen))
            } else {
                seen[c] = true;
                match &concepts[c] {
                    Concept::And(a, b) => {
                        let conjunctions = match push_pair(conjunctions, *a, (*b, c)) {
                            Some(list) => list,
                            None => return None,
                        };
                        let conjunctions = match push_pair(conjunctions, *b, (*a, c)) {
                            Some(list) => list,
                            None => return None,
                        };
                        let (conjunctions, existentials, seen) =
                            match register(concepts, conjunctions, existentials, seen, *a) {
                                Some(found) => found,
                                None => return None,
                            };
                        register(concepts, conjunctions, existentials, seen, *b)
                    }
                    Concept::Exists(r, f) => {
                        let existentials = match push_pair(existentials, *f, (*r, c)) {
                            Some(list) => list,
                            None => return None,
                        };
                        register(concepts, conjunctions, existentials, seen, *f)
                    }
                    _ => Some((conjunctions, existentials, seen)),
                }
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// The rules of `list[index..]` added to their indexes.
fn index_from(
    concepts: &Vec<Concept>,
    list: &Vec<Rule>,
    index: usize,
    rules: Rules,
    seen: Vec<bool>,
) -> Option<Rules> {
    if index < list.len() {
        match &list[index] {
            Rule::Sub(a, b) => {
                let told = match push_item(rules.told, *a, *b) {
                    Some(told) => told,
                    None => return None,
                };
                let (conjunctions, existentials, seen) =
                    match register(concepts, rules.conjunctions, rules.existentials, seen, *a) {
                        Some(found) => found,
                        None => return None,
                    };
                index_from(
                    concepts,
                    list,
                    index + 1,
                    Rules {
                        top: rules.top,
                        bottom: rules.bottom,
                        told,
                        conjunctions,
                        existentials,
                        supers: rules.supers,
                        firsts: rules.firsts,
                        seconds: rules.seconds,
                    },
                    seen,
                )
            }
            Rule::Role(r, s) => {
                let supers = match push_item(rules.supers, *r, *s) {
                    Some(supers) => supers,
                    None => return None,
                };
                index_from(
                    concepts,
                    list,
                    index + 1,
                    Rules {
                        top: rules.top,
                        bottom: rules.bottom,
                        told: rules.told,
                        conjunctions: rules.conjunctions,
                        existentials: rules.existentials,
                        supers,
                        firsts: rules.firsts,
                        seconds: rules.seconds,
                    },
                    seen,
                )
            }
            Rule::Chain(r1, r2, s) => {
                let firsts = match push_pair(rules.firsts, *r1, (*r2, *s)) {
                    Some(firsts) => firsts,
                    None => return None,
                };
                let seconds = match push_pair(rules.seconds, *r2, (*r1, *s)) {
                    Some(seconds) => seconds,
                    None => return None,
                };
                index_from(
                    concepts,
                    list,
                    index + 1,
                    Rules {
                        top: rules.top,
                        bottom: rules.bottom,
                        told: rules.told,
                        conjunctions: rules.conjunctions,
                        existentials: rules.existentials,
                        supers: rules.supers,
                        firsts,
                        seconds,
                    },
                    seen,
                )
            }
        }
    } else {
        Some(rules)
    }
}

fn has_from(list: &Vec<usize>, item: usize, index: usize) -> bool {
    if index < list.len() {
        if list[index] == item {
            true
        } else {
            has_from(list, item, index + 1)
        }
    } else {
        false
    }
}
fn has(list: &Vec<usize>, item: usize) -> bool {
    has_from(list, item, 0)
}
fn has_pair_from(list: &Vec<(usize, usize)>, first: usize, second: usize, index: usize) -> bool {
    if index < list.len() {
        let (a, b) = list[index];
        if a == first {
            if b == second {
                return true;
            }
        }
        has_pair_from(list, first, second, index + 1)
    } else {
        false
    }
}
fn has_pair(list: &Vec<(usize, usize)>, first: usize, second: usize) -> bool {
    has_pair_from(list, first, second, 0)
}

fn push_fact(mut queue: Vec<Fact>, fact: Fact) -> Option<Vec<Fact>> {
    if queue.len() < usize::MAX {
        queue.push(fact);
        Some(queue)
    } else {
        None
    }
}

/// Add the subsumer `c` of `x`.
fn add_sub(state: State, x: usize, c: usize) -> Option<State> {
    if x < state.subsumers.len() {
        if has(&state.subsumers[x], c) {
            Some(state)
        } else {
            let subsumers = match push_item(state.subsumers, x, c) {
                Some(subsumers) => subsumers,
                None => return None,
            };
            let queue = match push_fact(state.queue, Fact::Sub(x, c)) {
                Some(queue) => queue,
                None => return None,
            };
            Some(State {
                subsumers,
                active: state.active,
                out: state.out,
                into: state.into,
                queue,
                next: state.next,
            })
        }
    } else {
        None
    }
}
/// Add the link `x r y`.
fn add_link(state: State, x: usize, r: usize, y: usize) -> Option<State> {
    if x < state.out.len() {
        if has_pair(&state.out[x], r, y) {
            Some(state)
        } else {
            let out = match push_pair(state.out, x, (r, y)) {
                Some(out) => out,
                None => return None,
            };
            let into = match push_pair(state.into, y, (r, x)) {
                Some(into) => into,
                None => return None,
            };
            let queue = match push_fact(state.queue, Fact::Link(x, r, y)) {
                Some(queue) => queue,
                None => return None,
            };
            Some(State {
                subsumers: state.subsumers,
                active: state.active,
                out,
                into,
                queue,
                next: state.next,
            })
        }
    } else {
        None
    }
}
/// Make `x` a context: it subsumes itself and is subsumed by `owl:Thing`.
fn activate(mut state: State, x: usize, top: usize) -> Option<State> {
    if x < state.active.len() {
        if state.active[x] {
            Some(state)
        } else {
            state.active[x] = true;
            let state = match add_sub(state, x, x) {
                Some(state) => state,
                None => return None,
            };
            add_sub(state, x, top)
        }
    } else {
        None
    }
}

fn into_length(state: &State, x: usize) -> Option<usize> {
    if x < state.into.len() {
        Some(state.into[x].len())
    } else {
        None
    }
}
fn out_length(state: &State, x: usize) -> Option<usize> {
    if x < state.out.len() {
        Some(state.out[x].len())
    } else {
        None
    }
}
fn subsumers_length(state: &State, x: usize) -> Option<usize> {
    if x < state.subsumers.len() {
        Some(state.subsumers[x].len())
    } else {
        None
    }
}

/// `owl:Nothing` for every source of a link into `x`, from `into[x][index..end]`.
fn bottom_back(state: State, x: usize, c: usize, index: usize, end: usize) -> Option<State> {
    if index < end {
        if x < state.into.len() {
            if index < state.into[x].len() {
                let (_, w) = state.into[x][index];
                match add_sub(state, w, c) {
                    Some(state) => bottom_back(state, x, c, index + 1, end),
                    None => None,
                }
            } else {
                Some(state)
            }
        } else {
            None
        }
    } else {
        Some(state)
    }
}
/// The told subsumers `told[c][index..]` of `x`.
fn told_from(rules: &Rules, state: State, x: usize, c: usize, index: usize) -> Option<State> {
    if c < rules.told.len() {
        if index < rules.told[c].len() {
            match add_sub(state, x, rules.told[c][index]) {
                Some(state) => told_from(rules, state, x, c, index + 1),
                None => None,
            }
        } else {
            Some(state)
        }
    } else {
        None
    }
}
/// The conjunctions of `conjunctions[c][index..]` whose other part `x` has.
fn conjunctions_from(
    rules: &Rules,
    state: State,
    x: usize,
    c: usize,
    index: usize,
) -> Option<State> {
    if c < rules.conjunctions.len() {
        if index < rules.conjunctions[c].len() {
            if x < state.subsumers.len() {
                let (other, both) = rules.conjunctions[c][index];
                if has(&state.subsumers[x], other) {
                    match add_sub(state, x, both) {
                        Some(state) => conjunctions_from(rules, state, x, c, index + 1),
                        None => None,
                    }
                } else {
                    conjunctions_from(rules, state, x, c, index + 1)
                }
            } else {
                None
            }
        } else {
            Some(state)
        }
    } else {
        None
    }
}
/// The existential restrictions of `existentials[c][index..]` along `r`, for `w`.
fn existentials_from(
    rules: &Rules,
    state: State,
    w: usize,
    c: usize,
    r: usize,
    index: usize,
) -> Option<State> {
    if c < rules.existentials.len() {
        if index < rules.existentials[c].len() {
            let (s, e) = rules.existentials[c][index];
            if s == r {
                match add_sub(state, w, e) {
                    Some(state) => existentials_from(rules, state, w, c, r, index + 1),
                    None => None,
                }
            } else {
                existentials_from(rules, state, w, c, r, index + 1)
            }
        } else {
            Some(state)
        }
    } else {
        None
    }
}
/// The existential restrictions with filler `c` for the sources of the links
/// `into[x][index..end]`.
fn existentials_back(
    rules: &Rules,
    state: State,
    x: usize,
    c: usize,
    index: usize,
    end: usize,
) -> Option<State> {
    if index < end {
        if x < state.into.len() {
            if index < state.into[x].len() {
                let (r, w) = state.into[x][index];
                match existentials_from(rules, state, w, c, r, 0) {
                    Some(state) => existentials_back(rules, state, x, c, index + 1, end),
                    None => None,
                }
            } else {
                Some(state)
            }
        } else {
            None
        }
    } else {
        Some(state)
    }
}

/// The consequences of the new subsumer `c` of `x`.
fn process_sub(
    rules: &Rules,
    concepts: &Vec<Concept>,
    state: State,
    x: usize,
    c: usize,
) -> Option<State> {
    if c < concepts.len() {
        let state = match &concepts[c] {
            Concept::And(a, b) => {
                let state = match add_sub(state, x, *a) {
                    Some(state) => state,
                    None => return None,
                };
                match add_sub(state, x, *b) {
                    Some(state) => state,
                    None => return None,
                }
            }
            Concept::Exists(r, y) => match add_link(state, x, *r, *y) {
                Some(state) => state,
                None => return None,
            },
            Concept::Bottom => {
                let end = match into_length(&state, x) {
                    Some(end) => end,
                    None => return None,
                };
                match bottom_back(state, x, c, 0, end) {
                    Some(state) => state,
                    None => return None,
                }
            }
            _ => state,
        };
        let state = match told_from(rules, state, x, c, 0) {
            Some(state) => state,
            None => return None,
        };
        let state = match conjunctions_from(rules, state, x, c, 0) {
            Some(state) => state,
            None => return None,
        };
        let end = match into_length(&state, x) {
            Some(end) => end,
            None => return None,
        };
        existentials_back(rules, state, x, c, 0, end)
    } else {
        None
    }
}

/// For the subsumers `subsumers[y][index..end]` of the target of the new link
/// `x r y`: `owl:Nothing`, and the existential restrictions along `r`.
fn targets_from(
    rules: &Rules,
    state: State,
    x: usize,
    r: usize,
    y: usize,
    index: usize,
    end: usize,
) -> Option<State> {
    if index < end {
        if y < state.subsumers.len() {
            if index < state.subsumers[y].len() {
                let c = state.subsumers[y][index];
                let state = if c == rules.bottom {
                    match add_sub(state, x, c) {
                        Some(state) => state,
                        None => return None,
                    }
                } else {
                    state
                };
                match existentials_from(rules, state, x, c, r, 0) {
                    Some(state) => targets_from(rules, state, x, r, y, index + 1, end),
                    None => None,
                }
            } else {
                Some(state)
            }
        } else {
            None
        }
    } else {
        Some(state)
    }
}
/// The links `x s y` for the roles `s` of `supers[r][index..]`.
fn supers_from(
    rules: &Rules,
    state: State,
    x: usize,
    r: usize,
    y: usize,
    index: usize,
) -> Option<State> {
    if r < rules.supers.len() {
        if index < rules.supers[r].len() {
            match add_link(state, x, rules.supers[r][index], y) {
                Some(state) => supers_from(rules, state, x, r, y, index + 1),
                None => None,
            }
        } else {
            Some(state)
        }
    } else {
        None
    }
}
/// The links `x result z` for the links `y second z` of `out[y][index..end]`.
fn chain_out(
    state: State,
    x: usize,
    y: usize,
    second: usize,
    result: usize,
    index: usize,
    end: usize,
) -> Option<State> {
    if index < end {
        if y < state.out.len() {
            if index < state.out[y].len() {
                let (role, z) = state.out[y][index];
                if role == second {
                    match add_link(state, x, result, z) {
                        Some(state) => chain_out(state, x, y, second, result, index + 1, end),
                        None => None,
                    }
                } else {
                    chain_out(state, x, y, second, result, index + 1, end)
                }
            } else {
                Some(state)
            }
        } else {
            None
        }
    } else {
        Some(state)
    }
}
/// The chains of `firsts[r][index..]` started by the new link `x r y`.
fn firsts_from(
    rules: &Rules,
    state: State,
    x: usize,
    r: usize,
    y: usize,
    index: usize,
) -> Option<State> {
    if r < rules.firsts.len() {
        if index < rules.firsts[r].len() {
            let (second, result) = rules.firsts[r][index];
            let end = match out_length(&state, y) {
                Some(end) => end,
                None => return None,
            };
            match chain_out(state, x, y, second, result, 0, end) {
                Some(state) => firsts_from(rules, state, x, r, y, index + 1),
                None => None,
            }
        } else {
            Some(state)
        }
    } else {
        None
    }
}
/// The links `w result y` for the links `w first x` of `into[x][index..end]`.
fn chain_in(
    state: State,
    x: usize,
    y: usize,
    first: usize,
    result: usize,
    index: usize,
    end: usize,
) -> Option<State> {
    if index < end {
        if x < state.into.len() {
            if index < state.into[x].len() {
                let (role, w) = state.into[x][index];
                if role == first {
                    match add_link(state, w, result, y) {
                        Some(state) => chain_in(state, x, y, first, result, index + 1, end),
                        None => None,
                    }
                } else {
                    chain_in(state, x, y, first, result, index + 1, end)
                }
            } else {
                Some(state)
            }
        } else {
            None
        }
    } else {
        Some(state)
    }
}
/// The chains of `seconds[r][index..]` ended by the new link `x r y`.
fn seconds_from(
    rules: &Rules,
    state: State,
    x: usize,
    r: usize,
    y: usize,
    index: usize,
) -> Option<State> {
    if r < rules.seconds.len() {
        if index < rules.seconds[r].len() {
            let (first, result) = rules.seconds[r][index];
            let end = match into_length(&state, x) {
                Some(end) => end,
                None => return None,
            };
            match chain_in(state, x, y, first, result, 0, end) {
                Some(state) => seconds_from(rules, state, x, r, y, index + 1),
                None => None,
            }
        } else {
            Some(state)
        }
    } else {
        None
    }
}

/// The consequences of the new link `x r y`.
fn process_link(rules: &Rules, state: State, x: usize, r: usize, y: usize) -> Option<State> {
    let state = match activate(state, y, rules.top) {
        Some(state) => state,
        None => return None,
    };
    let end = match subsumers_length(&state, y) {
        Some(end) => end,
        None => return None,
    };
    let state = match targets_from(rules, state, x, r, y, 0, end) {
        Some(state) => state,
        None => return None,
    };
    let state = match supers_from(rules, state, x, r, y, 0) {
        Some(state) => state,
        None => return None,
    };
    let state = match firsts_from(rules, state, x, r, y, 0) {
        Some(state) => state,
        None => return None,
    };
    seconds_from(rules, state, x, r, y, 0)
}

/// Process queued facts until none is left, or `None` when `fuel` runs out.
fn saturate(rules: &Rules, concepts: &Vec<Concept>, state: State, fuel: usize) -> Option<State> {
    if state.next < state.queue.len() {
        if fuel == 0 {
            None
        } else {
            let fact = match &state.queue[state.next] {
                Fact::Sub(x, c) => Fact::Sub(*x, *c),
                Fact::Link(x, r, y) => Fact::Link(*x, *r, *y),
            };
            let state = State {
                subsumers: state.subsumers,
                active: state.active,
                out: state.out,
                into: state.into,
                queue: state.queue,
                next: state.next + 1,
            };
            let state = match fact {
                Fact::Sub(x, c) => match process_sub(rules, concepts, state, x, c) {
                    Some(state) => state,
                    None => return None,
                },
                Fact::Link(x, r, y) => match process_link(rules, state, x, r, y) {
                    Some(state) => state,
                    None => return None,
                },
            };
            saturate(rules, concepts, state, fuel - 1)
        }
    } else {
        Some(state)
    }
}

fn told_closed(told: &Vec<usize>, list: &Vec<usize>, index: usize) -> bool {
    if index < told.len() {
        if has(list, told[index]) {
            told_closed(told, list, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn conjunctions_closed(
    conjunctions: &Vec<(usize, usize)>,
    list: &Vec<usize>,
    index: usize,
) -> bool {
    if index < conjunctions.len() {
        let (other, both) = conjunctions[index];
        if has(list, other) {
            if has(list, both) {
                conjunctions_closed(conjunctions, list, index + 1)
            } else {
                false
            }
        } else {
            conjunctions_closed(conjunctions, list, index + 1)
        }
    } else {
        true
    }
}
/// The parts of a conjunction `c` are in `list`, and the link of an
/// existential restriction `c` is in `links`.
fn parts_closed(
    concepts: &Vec<Concept>,
    c: usize,
    list: &Vec<usize>,
    links: &Vec<(usize, usize)>,
) -> bool {
    if c < concepts.len() {
        match &concepts[c] {
            Concept::And(a, b) => {
                if has(list, *a) {
                    has(list, *b)
                } else {
                    false
                }
            }
            Concept::Exists(r, y) => has_pair(links, *r, *y),
            _ => true,
        }
    } else {
        false
    }
}
/// The subsumers `list[index..]` of a context with links `links` have their
/// parts, links, told subsumers and conjunctions.
fn subsumers_closed(
    rules: &Rules,
    concepts: &Vec<Concept>,
    list: &Vec<usize>,
    links: &Vec<(usize, usize)>,
    index: usize,
) -> bool {
    if index < list.len() {
        let c = list[index];
        if c < rules.told.len() {
            if c < rules.conjunctions.len() {
                if parts_closed(concepts, c, list, links) {
                    if told_closed(&rules.told[c], list, 0) {
                        if conjunctions_closed(&rules.conjunctions[c], list, 0) {
                            return subsumers_closed(rules, concepts, list, links, index + 1);
                        }
                    }
                }
            }
        }
        false
    } else {
        true
    }
}
fn existentials_closed(
    existentials: &Vec<(usize, usize)>,
    list: &Vec<usize>,
    r: usize,
    index: usize,
) -> bool {
    if index < existentials.len() {
        let (s, e) = existentials[index];
        if s == r {
            if has(list, e) {
                existentials_closed(existentials, list, r, index + 1)
            } else {
                false
            }
        } else {
            existentials_closed(existentials, list, r, index + 1)
        }
    } else {
        true
    }
}
/// Every subsumer `target[index..]` of the target of a link along `r` from a
/// context with subsumers `list` has its existential restrictions along `r`
/// in `list`.
fn targets_closed(
    rules: &Rules,
    list: &Vec<usize>,
    target: &Vec<usize>,
    r: usize,
    index: usize,
) -> bool {
    if index < target.len() {
        let c = target[index];
        if c < rules.existentials.len() {
            if existentials_closed(&rules.existentials[c], list, r, 0) {
                return targets_closed(rules, list, target, r, index + 1);
            }
        }
        false
    } else {
        true
    }
}
fn supers_closed(supers: &Vec<usize>, links: &Vec<(usize, usize)>, y: usize, index: usize) -> bool {
    if index < supers.len() {
        if has_pair(links, supers[index], y) {
            supers_closed(supers, links, y, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn chain_closed(
    links: &Vec<(usize, usize)>,
    onward: &Vec<(usize, usize)>,
    second: usize,
    result: usize,
    index: usize,
) -> bool {
    if index < onward.len() {
        let (role, z) = onward[index];
        if role == second {
            if has_pair(links, result, z) {
                chain_closed(links, onward, second, result, index + 1)
            } else {
                false
            }
        } else {
            chain_closed(links, onward, second, result, index + 1)
        }
    } else {
        true
    }
}
fn firsts_closed(
    firsts: &Vec<(usize, usize)>,
    links: &Vec<(usize, usize)>,
    onward: &Vec<(usize, usize)>,
    index: usize,
) -> bool {
    if index < firsts.len() {
        let (second, result) = firsts[index];
        if chain_closed(links, onward, second, result, 0) {
            firsts_closed(firsts, links, onward, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// `owl:Nothing` at a context with subsumers `list` when the target of one
/// of its links has it.
fn back_closed(list: &Vec<usize>, target: &Vec<usize>, bottom: usize) -> bool {
    if has(target, bottom) {
        has(list, bottom)
    } else {
        true
    }
}
/// The link `x r y` leads to a context, carries `owl:Nothing` and the
/// existential restrictions back, and is closed under inclusions and chains.
fn link_closed(rules: &Rules, state: &State, x: usize, r: usize, y: usize) -> bool {
    if x < state.subsumers.len() {
        if x < state.out.len() {
            if y < state.subsumers.len() {
                if y < state.active.len() {
                    if y < state.out.len() {
                        if r < rules.supers.len() {
                            if r < rules.firsts.len() {
                                if state.active[y] {
                                    if back_closed(
                                        &state.subsumers[x],
                                        &state.subsumers[y],
                                        rules.bottom,
                                    ) {
                                        if targets_closed(
                                            rules,
                                            &state.subsumers[x],
                                            &state.subsumers[y],
                                            r,
                                            0,
                                        ) {
                                            if supers_closed(&rules.supers[r], &state.out[x], y, 0)
                                            {
                                                return firsts_closed(
                                                    &rules.firsts[r],
                                                    &state.out[x],
                                                    &state.out[y],
                                                    0,
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    false
}
/// The links `out[x][index..]` are closed.
fn links_closed(rules: &Rules, state: &State, x: usize, index: usize) -> bool {
    if x < state.out.len() {
        if index < state.out[x].len() {
            let (r, y) = state.out[x][index];
            if link_closed(rules, state, x, r, y) {
                links_closed(rules, state, x, index + 1)
            } else {
                false
            }
        } else {
            true
        }
    } else {
        false
    }
}
/// An active context subsumes itself and is subsumed by `owl:Thing`; an
/// inactive one has no subsumers.
fn start_closed(active: bool, list: &Vec<usize>, x: usize, top: usize) -> bool {
    if active {
        if has(list, x) {
            has(list, top)
        } else {
            false
        }
    } else {
        list.len() == 0
    }
}
/// Every context of `x..` is closed.
fn contexts_closed(rules: &Rules, concepts: &Vec<Concept>, state: &State, x: usize) -> bool {
    if x < state.subsumers.len() {
        if x < state.active.len() {
            if x < state.out.len() {
                if start_closed(state.active[x], &state.subsumers[x], x, rules.top) {
                    if subsumers_closed(rules, concepts, &state.subsumers[x], &state.out[x], 0) {
                        if links_closed(rules, state, x, 0) {
                            return contexts_closed(rules, concepts, state, x + 1);
                        }
                    }
                }
            }
        }
        false
    } else {
        true
    }
}

/// Whether every rule's conclusion is present wherever its premises are.
pub fn closed(rules: &Rules, concepts: &Vec<Concept>, state: &State) -> bool {
    let count = concepts.len();
    if state.subsumers.len() == count {
        if state.active.len() == count {
            if state.out.len() == count {
                if rules.top < count {
                    if rules.bottom < count {
                        return contexts_closed(rules, concepts, state, 0);
                    }
                }
            }
        }
    }
    false
}

/// The concepts of `classes[index..]` added to `out`.
fn class_concepts(
    table: Table,
    classes: &Vec<Class>,
    index: usize,
    mut out: Vec<usize>,
) -> Option<(Table, Vec<usize>)> {
    if index < classes.len() {
        let (table, id) =
            match concept_of(table, &ClassExpression::Class(copy_class(&classes[index]))) {
                Some(pair) => pair,
                None => return None,
            };
        if out.len() < usize::MAX {
            out.push(id);
            class_concepts(table, classes, index + 1, out)
        } else {
            None
        }
    } else {
        Some((table, out))
    }
}

fn activate_all(state: State, ids: &Vec<usize>, top: usize, index: usize) -> Option<State> {
    if index < ids.len() {
        match activate(state, ids[index], top) {
            Some(state) => activate_all(state, ids, top, index + 1),
            None => None,
        }
    } else {
        Some(state)
    }
}

/// The table, the indexed rules, the closed saturated state and the concepts
/// of the classes.
pub fn saturated(
    items: &Vec<AnnotatedAxiom>,
    classes: &Vec<Class>,
) -> Option<(Table, Rules, State, Vec<usize>)> {
    let (table, top) = match intern(empty_table(), Concept::Top) {
        Some(pair) => pair,
        None => return None,
    };
    let (table, bottom) = match intern(table, Concept::Bottom) {
        Some(pair) => pair,
        None => return None,
    };
    let (table, list) = match translate(table, Vec::new(), items, top, bottom, 0) {
        Some(pair) => pair,
        None => return None,
    };
    let (table, ids) = match class_concepts(table, classes, 0, Vec::new()) {
        Some(pair) => pair,
        None => return None,
    };
    let count = table.concepts.len();
    let roles = table.roles.len();
    let empty = Rules {
        top,
        bottom,
        told: empty_lists(count, Vec::new()),
        conjunctions: empty_pairs(count, Vec::new()),
        existentials: empty_pairs(count, Vec::new()),
        supers: empty_lists(roles, Vec::new()),
        firsts: empty_pairs(roles, Vec::new()),
        seconds: empty_pairs(roles, Vec::new()),
    };
    let rules = match index_from(&table.concepts, &list, 0, empty, falses(count, Vec::new())) {
        Some(rules) => rules,
        None => return None,
    };
    let state = State {
        subsumers: empty_lists(count, Vec::new()),
        active: falses(count, Vec::new()),
        out: empty_pairs(count, Vec::new()),
        into: empty_pairs(count, Vec::new()),
        queue: Vec::new(),
        next: 0,
    };
    let state = match activate(state, top, top) {
        Some(state) => state,
        None => return None,
    };
    let state = match activate_all(state, &ids, top, 0) {
        Some(state) => state,
        None => return None,
    };
    let state = match saturate(&rules, &table.concepts, state, usize::MAX) {
        Some(state) => state,
        None => return None,
    };
    if closed(&rules, &table.concepts, &state) {
        Some((table, rules, state, ids))
    } else {
        None
    }
}

/// The row of answers of a class with subsumers `list`: whether it is
/// subsumed by each class of `ids[index..]`.
fn row_from(
    list: &Vec<usize>,
    empty: bool,
    ids: &Vec<usize>,
    index: usize,
    mut out: Vec<bool>,
) -> Option<Vec<bool>> {
    if index < ids.len() {
        if out.len() < usize::MAX {
            out.push(if empty { true } else { has(list, ids[index]) });
            row_from(list, empty, ids, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The answers for the classes `ids[index..]`.
fn answers_from(
    state: &State,
    bottom: usize,
    inconsistent: bool,
    ids: &Vec<usize>,
    index: usize,
    mut satisfiable: Vec<bool>,
    mut subsumed: Vec<Vec<bool>>,
) -> Option<Classification> {
    if index < ids.len() {
        let id = ids[index];
        if id < state.subsumers.len() {
            let empty = if inconsistent {
                true
            } else {
                has(&state.subsumers[id], bottom)
            };
            let row = match row_from(&state.subsumers[id], empty, ids, 0, Vec::new()) {
                Some(row) => row,
                None => return None,
            };
            if satisfiable.len() < usize::MAX {
                if subsumed.len() < usize::MAX {
                    satisfiable.push(!empty);
                    subsumed.push(row);
                    answers_from(
                        state,
                        bottom,
                        inconsistent,
                        ids,
                        index + 1,
                        satisfiable,
                        subsumed,
                    )
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(Classification {
            satisfiable,
            subsumed,
        })
    }
}

/// Classify the named classes of an EL ontology: for every listed class
/// whether it is satisfiable and, for every pair, whether the first is
/// subsumed by the second; `None` outside the EL fragment.
pub fn classify(items: &Vec<AnnotatedAxiom>, classes: &Vec<Class>) -> Option<Classification> {
    let (_, rules, state, ids) = match saturated(items, classes) {
        Some(found) => found,
        None => return None,
    };
    if rules.top < state.subsumers.len() {
        let inconsistent = has(&state.subsumers[rules.top], rules.bottom);
        answers_from(
            &state,
            rules.bottom,
            inconsistent,
            &ids,
            0,
            Vec::new(),
            Vec::new(),
        )
    } else {
        None
    }
}

/// Whether the axioms of an EL ontology have a model: whether `owl:Nothing`
/// does not subsume `owl:Thing`; `None` outside the EL fragment.
pub fn consistent(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    let (_, rules, state, _) = match saturated(items, &Vec::new()) {
        Some(found) => found,
        None => return None,
    };
    if rules.top < state.subsumers.len() {
        Some(!has(&state.subsumers[rules.top], rules.bottom))
    } else {
        None
    }
}

/// The classification of the listed named classes as lists: whether each class
/// is satisfiable and, for a satisfiable class, the positions of the listed
/// classes that subsume it (its own among them). An unsatisfiable class is
/// subsumed by every class and lists none.
pub struct Taxonomy {
    pub satisfiable: Vec<bool>,
    pub supers: Vec<Vec<usize>>,
}

/// For every concept, the positions of the classes `ids[index..]` with that
/// concept, added to `out`.
fn positions_from(ids: &Vec<usize>, index: usize, out: Vec<Vec<usize>>) -> Option<Vec<Vec<usize>>> {
    if index < ids.len() {
        match push_item(out, ids[index], index) {
            Some(out) => positions_from(ids, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `items[index..]` added to `out`.
fn append_from(items: &Vec<usize>, index: usize, mut out: Vec<usize>) -> Option<Vec<usize>> {
    if index < items.len() {
        if out.len() < usize::MAX {
            out.push(items[index]);
            append_from(items, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The positions of the classes whose concepts are among `list[index..]`,
/// added to `out`.
fn positions_of(
    list: &Vec<usize>,
    positions: &Vec<Vec<usize>>,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < list.len() {
        let c = list[index];
        if c < positions.len() {
            match append_from(&positions[c], 0, out) {
                Some(out) => positions_of(list, positions, index + 1, out),
                None => None,
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The answers for the classes `ids[index..]`.
fn taxonomy_from(
    state: &State,
    bottom: usize,
    inconsistent: bool,
    ids: &Vec<usize>,
    positions: &Vec<Vec<usize>>,
    index: usize,
    mut satisfiable: Vec<bool>,
    mut supers: Vec<Vec<usize>>,
) -> Option<Taxonomy> {
    if index < ids.len() {
        let id = ids[index];
        if id < state.subsumers.len() {
            let empty = if inconsistent {
                true
            } else {
                has(&state.subsumers[id], bottom)
            };
            let list = if empty {
                Vec::new()
            } else {
                match positions_of(&state.subsumers[id], positions, 0, Vec::new()) {
                    Some(list) => list,
                    None => return None,
                }
            };
            if satisfiable.len() < usize::MAX {
                if supers.len() < usize::MAX {
                    satisfiable.push(!empty);
                    supers.push(list);
                    taxonomy_from(
                        state,
                        bottom,
                        inconsistent,
                        ids,
                        positions,
                        index + 1,
                        satisfiable,
                        supers,
                    )
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(Taxonomy {
            satisfiable,
            supers,
        })
    }
}

/// Classify the named classes of an EL ontology as lists: for every listed
/// class whether it is satisfiable and, if so, the positions of the listed
/// classes that subsume it; `None` outside the EL fragment. Unlike `classify`
/// it takes space in proportion to the subsumptions, not to the pairs.
pub fn taxonomy(items: &Vec<AnnotatedAxiom>, classes: &Vec<Class>) -> Option<Taxonomy> {
    let (table, rules, state, ids) = match saturated(items, classes) {
        Some(found) => found,
        None => return None,
    };
    let positions = match positions_from(&ids, 0, empty_lists(table.concepts.len(), Vec::new())) {
        Some(positions) => positions,
        None => return None,
    };
    if rules.top < state.subsumers.len() {
        let inconsistent = has(&state.subsumers[rules.top], rules.bottom);
        taxonomy_from(
            &state,
            rules.bottom,
            inconsistent,
            &ids,
            &positions,
            0,
            Vec::new(),
            Vec::new(),
        )
    } else {
        None
    }
}
