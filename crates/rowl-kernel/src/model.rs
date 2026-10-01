//! M2 structural representation of standard OWL 2 DL.
//!
//! These are raw, role-typed structures, not a validated ontology. Lexical IRI
//! validity, canonical set associations, declaration typing, datatype lexical
//! spaces and global DL restrictions are separate M3–M5 obligations. Nonempty
//! and minimum written arities are enforced by construction. Property chains
//! retain order and repetitions; other associations require canonicalization.

use crate::probes::Natural;

/// Exact UTF-8 byte spelling. This raw type does not certify UTF-8 or IRI
/// lexical validity; those checks belong to the verified frontend.
pub struct Iri {
    pub spelling: Vec<u8>,
}

pub struct Class {
    pub iri: Iri,
}
pub struct Datatype {
    pub iri: Iri,
}
pub struct ObjectProperty {
    pub iri: Iri,
}
pub struct DataProperty {
    pub iri: Iri,
}
pub struct AnnotationProperty {
    pub iri: Iri,
}
pub struct NamedIndividual {
    pub iri: Iri,
}

/// Opaque ontology scope assigned when anonymous individuals are standardized
/// apart. Different scope tokens do not imply different logical denotations.
/// Scope and local label are exact raw byte spellings; frontend validation and
/// the verified import assembler will establish their lexical/scoping rules.
pub struct AnonymousIndividual {
    pub scope: Vec<u8>,
    pub label: Vec<u8>,
}

pub enum Individual {
    Named(NamedIndividual),
    Anonymous(AnonymousIndividual),
}

/// Structural literals have a lexical form and datatype. The frontend will
/// expand string/language abbreviations into this representation.
/// The exact raw bytes are not a datatype value or a UTF-8 validity certificate.
pub struct Literal {
    pub lexical: Vec<u8>,
    pub datatype: Datatype,
}

pub struct NonEmpty<T> {
    pub first: T,
    pub rest: Vec<T>,
}

pub struct AtLeastTwo<T> {
    pub first: T,
    pub second: T,
    pub rest: Vec<T>,
}

pub enum Entity {
    Class(Class),
    Datatype(Datatype),
    ObjectProperty(ObjectProperty),
    DataProperty(DataProperty),
    AnnotationProperty(AnnotationProperty),
    NamedIndividual(NamedIndividual),
}

pub enum ObjectPropertyExpression {
    Property(ObjectProperty),
    Inverse(ObjectProperty),
}

/// Inversion changes orientation without changing the property identity.
pub fn invert(property: ObjectPropertyExpression) -> ObjectPropertyExpression {
    match property {
        ObjectPropertyExpression::Property(p) => ObjectPropertyExpression::Inverse(p),
        ObjectPropertyExpression::Inverse(p) => ObjectPropertyExpression::Property(p),
    }
}

pub struct FacetRestriction {
    pub facet: Iri,
    pub value: Literal,
}

pub enum DataRange {
    Datatype(Datatype),
    Intersection(Box<AtLeastTwo<DataRange>>),
    Union(Box<AtLeastTwo<DataRange>>),
    Complement(Box<DataRange>),
    OneOf(NonEmpty<Literal>),
    Restriction(Datatype, NonEmpty<FacetRestriction>),
}

/// All standard OWL 2 data ranges are unary. Nonstandard n-ary datatype hooks
/// are outside this representation, so data quantifiers have one property.
pub enum ClassExpression {
    Class(Class),
    ObjectIntersectionOf(Box<AtLeastTwo<ClassExpression>>),
    ObjectUnionOf(Box<AtLeastTwo<ClassExpression>>),
    ObjectComplementOf(Box<ClassExpression>),
    ObjectOneOf(NonEmpty<Individual>),
    ObjectSomeValuesFrom(ObjectPropertyExpression, Box<ClassExpression>),
    ObjectAllValuesFrom(ObjectPropertyExpression, Box<ClassExpression>),
    ObjectHasValue(ObjectPropertyExpression, Individual),
    ObjectHasSelf(ObjectPropertyExpression),
    ObjectMinCardinality(
        Natural,
        ObjectPropertyExpression,
        Option<Box<ClassExpression>>,
    ),
    ObjectMaxCardinality(
        Natural,
        ObjectPropertyExpression,
        Option<Box<ClassExpression>>,
    ),
    ObjectExactCardinality(
        Natural,
        ObjectPropertyExpression,
        Option<Box<ClassExpression>>,
    ),
    DataSomeValuesFrom(DataProperty, DataRange),
    DataAllValuesFrom(DataProperty, DataRange),
    DataHasValue(DataProperty, Literal),
    DataMinCardinality(Natural, DataProperty, Option<DataRange>),
    DataMaxCardinality(Natural, DataProperty, Option<DataRange>),
    DataExactCardinality(Natural, DataProperty, Option<DataRange>),
}

pub enum AnnotationSubject {
    Iri(Iri),
    Anonymous(AnonymousIndividual),
}

pub enum AnnotationValue {
    Iri(Iri),
    Anonymous(AnonymousIndividual),
    Literal(Literal),
}

pub struct Annotation {
    pub annotations: Vec<Annotation>,
    pub property: AnnotationProperty,
    pub value: AnnotationValue,
}

pub enum SubObjectPropertyExpression {
    Single(ObjectPropertyExpression),
    Chain(AtLeastTwo<ObjectPropertyExpression>),
}

pub enum Axiom {
    Declaration(Entity),
    SubClassOf(ClassExpression, ClassExpression),
    EquivalentClasses(AtLeastTwo<ClassExpression>),
    DisjointClasses(AtLeastTwo<ClassExpression>),
    DisjointUnion(Class, AtLeastTwo<ClassExpression>),
    SubObjectPropertyOf(SubObjectPropertyExpression, ObjectPropertyExpression),
    EquivalentObjectProperties(AtLeastTwo<ObjectPropertyExpression>),
    DisjointObjectProperties(AtLeastTwo<ObjectPropertyExpression>),
    InverseObjectProperties(ObjectPropertyExpression, ObjectPropertyExpression),
    ObjectPropertyDomain(ObjectPropertyExpression, ClassExpression),
    ObjectPropertyRange(ObjectPropertyExpression, ClassExpression),
    FunctionalObjectProperty(ObjectPropertyExpression),
    InverseFunctionalObjectProperty(ObjectPropertyExpression),
    ReflexiveObjectProperty(ObjectPropertyExpression),
    IrreflexiveObjectProperty(ObjectPropertyExpression),
    SymmetricObjectProperty(ObjectPropertyExpression),
    AsymmetricObjectProperty(ObjectPropertyExpression),
    TransitiveObjectProperty(ObjectPropertyExpression),
    SubDataPropertyOf(DataProperty, DataProperty),
    EquivalentDataProperties(AtLeastTwo<DataProperty>),
    DisjointDataProperties(AtLeastTwo<DataProperty>),
    DataPropertyDomain(DataProperty, ClassExpression),
    DataPropertyRange(DataProperty, DataRange),
    FunctionalDataProperty(DataProperty),
    DatatypeDefinition(Datatype, DataRange),
    HasKey(
        ClassExpression,
        Vec<ObjectPropertyExpression>,
        Vec<DataProperty>,
    ),
    SameIndividual(AtLeastTwo<Individual>),
    DifferentIndividuals(AtLeastTwo<Individual>),
    ClassAssertion(ClassExpression, Individual),
    ObjectPropertyAssertion(ObjectPropertyExpression, Individual, Individual),
    NegativeObjectPropertyAssertion(ObjectPropertyExpression, Individual, Individual),
    DataPropertyAssertion(DataProperty, Individual, Literal),
    NegativeDataPropertyAssertion(DataProperty, Individual, Literal),
    AnnotationAssertion(AnnotationProperty, AnnotationSubject, AnnotationValue),
    SubAnnotationPropertyOf(AnnotationProperty, AnnotationProperty),
    AnnotationPropertyDomain(AnnotationProperty, Iri),
    AnnotationPropertyRange(AnnotationProperty, Iri),
}

pub struct AnnotatedAxiom {
    pub annotations: Vec<Annotation>,
    pub axiom: Axiom,
}

/// A version IRI cannot exist without an ontology IRI.
pub enum OntologyIdentity {
    Anonymous,
    Named { ontology: Iri, version: Option<Iri> },
}

pub struct RawOntology {
    pub identity: OntologyIdentity,
    pub imports: Vec<Iri>,
    pub annotations: Vec<Annotation>,
    pub axioms: Vec<AnnotatedAxiom>,
}
