//! The kernel's raw OWL model of a read Functional Syntax document.
//!
//! Every source record maps to the structural model with its exact IRI and
//! literal bytes; node IDs become anonymous individuals in the caller's scope,
//! and original tokens are dropped. The mapping fails only on a member list
//! with fewer than two members or an empty enumeration, which the proved
//! document reader never produces.
#![allow(clippy::ptr_arg, clippy::question_mark, clippy::manual_map)] // Explicit branches for the pinned extraction subset.
use crate::functional_annotation_axioms::{SourceAnnotationAxiomBody, SourceAnnotationSubject};
use crate::functional_annotations::{SourceAnnotation, SourceAnnotationValue};
use crate::functional_assertions::SourceAssertionBody;
use crate::functional_class_axioms::SourceClassAxiomBody;
use crate::functional_classes::{Bound, SourceClass, SourceObjectProperty};
use crate::functional_declarations::{SourceEntity, SourceEntityKind};
use crate::functional_document::{SourceAxiom, SourceDocument};
use crate::functional_header::{HeaderIri, ImportReference, SourceOntologyIdentity};
use crate::functional_individuals::SourceIndividual;
use crate::functional_literals::SourceLiteral;
use crate::functional_property_axioms::{
    PropertyCharacteristic, SourcePropertyAxiomBody, SourceSubProperty,
};
use crate::functional_ranges::{SourceDataRange, SourceFacet};
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationProperty, AnnotationSubject, AnnotationValue,
    AnonymousIndividual, AtLeastTwo, Axiom, Class, ClassExpression, DataProperty, DataRange,
    Datatype, Entity, FacetRestriction, Individual, Iri, Literal, NamedIndividual, NonEmpty,
    ObjectProperty, ObjectPropertyExpression, OntologyIdentity, RawOntology,
    SubObjectPropertyExpression,
};
use crate::probes::Natural;

fn copy_from(source: &Vec<u8>, index: usize, mut target: Vec<u8>) -> Vec<u8> {
    if index < source.len() {
        target.push(source[index]);
        copy_from(source, index + 1, target)
    } else {
        target
    }
}
fn copy_bytes(source: &Vec<u8>) -> Vec<u8> {
    copy_from(source, 0, Vec::new())
}
fn iri(source: &HeaderIri) -> Iri {
    Iri {
        spelling: copy_bytes(&source.value),
    }
}
fn anonymous(label: &Vec<u8>, scope: &Vec<u8>) -> AnonymousIndividual {
    AnonymousIndividual {
        scope: copy_bytes(scope),
        label: copy_bytes(label),
    }
}
fn literal(source: &SourceLiteral) -> Literal {
    Literal {
        lexical: copy_bytes(&source.lexical),
        datatype: Datatype {
            iri: Iri {
                spelling: copy_bytes(&source.datatype),
            },
        },
    }
}
fn annotation_value(source: &SourceAnnotationValue, scope: &Vec<u8>) -> AnnotationValue {
    match source {
        SourceAnnotationValue::Iri(value) => AnnotationValue::Iri(iri(value)),
        SourceAnnotationValue::Anonymous { label, .. } => {
            AnnotationValue::Anonymous(anonymous(label, scope))
        }
        SourceAnnotationValue::Literal(value) => AnnotationValue::Literal(literal(value)),
    }
}
fn annotation(source: &SourceAnnotation, scope: &Vec<u8>) -> Annotation {
    Annotation {
        annotations: annotations_from(&source.annotations, 0, Vec::new(), scope),
        property: AnnotationProperty {
            iri: iri(&source.property),
        },
        value: annotation_value(&source.value, scope),
    }
}
fn annotations_from(
    values: &Vec<SourceAnnotation>,
    index: usize,
    mut out: Vec<Annotation>,
    scope: &Vec<u8>,
) -> Vec<Annotation> {
    if index < values.len() {
        out.push(annotation(&values[index], scope));
        annotations_from(values, index + 1, out, scope)
    } else {
        out
    }
}
fn property(source: &SourceObjectProperty) -> ObjectPropertyExpression {
    match source {
        SourceObjectProperty::Named(name) => {
            ObjectPropertyExpression::Property(ObjectProperty { iri: iri(name) })
        }
        SourceObjectProperty::Inverse { property, .. } => {
            ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(property) })
        }
    }
}
fn individual(source: &SourceIndividual, scope: &Vec<u8>) -> Individual {
    match source {
        SourceIndividual::Named(name) => Individual::Named(NamedIndividual { iri: iri(name) }),
        SourceIndividual::Anonymous { label, .. } => Individual::Anonymous(anonymous(label, scope)),
    }
}
/// The model of `values[index..]` after `out`.
fn individuals_from(
    values: &Vec<SourceIndividual>,
    index: usize,
    mut out: Vec<Individual>,
    scope: &Vec<u8>,
) -> Vec<Individual> {
    if index < values.len() && out.len() < values.len() {
        out.push(individual(&values[index], scope));
        individuals_from(values, index + 1, out, scope)
    } else {
        out
    }
}
/// An enumeration of at least one individual.
#[allow(clippy::len_zero)] // Vec::is_empty lacks a model in the pinned extraction.
fn enumeration(values: &Vec<SourceIndividual>, scope: &Vec<u8>) -> Option<NonEmpty<Individual>> {
    if values.len() < 1 {
        return None;
    }
    Some(NonEmpty {
        first: individual(&values[0], scope),
        rest: individuals_from(values, 1, Vec::new(), scope),
    })
}
/// A member list of at least two individuals.
fn individual_members(
    values: &Vec<SourceIndividual>,
    scope: &Vec<u8>,
) -> Option<AtLeastTwo<Individual>> {
    if values.len() < 2 {
        return None;
    }
    Some(AtLeastTwo {
        first: individual(&values[0], scope),
        second: individual(&values[1], scope),
        rest: individuals_from(values, 2, Vec::new(), scope),
    })
}
/// The model of `values[index..]` after `out`.
fn literals_from(values: &Vec<SourceLiteral>, index: usize, mut out: Vec<Literal>) -> Vec<Literal> {
    if index < values.len() && out.len() < values.len() {
        out.push(literal(&values[index]));
        literals_from(values, index + 1, out)
    } else {
        out
    }
}
/// The model of `values[index..]` after `out`.
fn facets_from(
    values: &Vec<SourceFacet>,
    index: usize,
    mut out: Vec<FacetRestriction>,
) -> Vec<FacetRestriction> {
    if index < values.len() && out.len() < values.len() {
        out.push(FacetRestriction {
            facet: iri(&values[index].facet),
            value: literal(&values[index].value),
        });
        facets_from(values, index + 1, out)
    } else {
        out
    }
}
/// A data range of the model; `None` for a member list with fewer than two
/// members or an enumeration or restriction without members.
#[allow(clippy::len_zero)] // Vec::is_empty lacks a model in the pinned extraction.
fn data_range(source: &SourceDataRange) -> Option<DataRange> {
    match source {
        SourceDataRange::Datatype(name) => Some(DataRange::Datatype(Datatype { iri: iri(name) })),
        SourceDataRange::IntersectionOf { members, .. } => match range_members(members) {
            Some(members) => Some(DataRange::Intersection(Box::new(members))),
            None => None,
        },
        SourceDataRange::UnionOf { members, .. } => match range_members(members) {
            Some(members) => Some(DataRange::Union(Box::new(members))),
            None => None,
        },
        SourceDataRange::ComplementOf { operand, .. } => match data_range(operand) {
            Some(operand) => Some(DataRange::Complement(Box::new(operand))),
            None => None,
        },
        SourceDataRange::OneOf { members, .. } => {
            if members.len() < 1 {
                return None;
            }
            Some(DataRange::OneOf(NonEmpty {
                first: literal(&members[0]),
                rest: literals_from(members, 1, Vec::new()),
            }))
        }
        SourceDataRange::Restriction {
            datatype, facets, ..
        } => {
            if facets.len() < 1 {
                return None;
            }
            Some(DataRange::Restriction(
                Datatype { iri: iri(datatype) },
                NonEmpty {
                    first: FacetRestriction {
                        facet: iri(&facets[0].facet),
                        value: literal(&facets[0].value),
                    },
                    rest: facets_from(facets, 1, Vec::new()),
                },
            ))
        }
    }
}
/// The model of the data ranges `values[index..]` after `out`.
fn range_rest_from(
    values: &Vec<SourceDataRange>,
    index: usize,
    mut out: Vec<DataRange>,
) -> Option<Vec<DataRange>> {
    if index < values.len() {
        match data_range(&values[index]) {
            Some(value) => {
                out.push(value);
                range_rest_from(values, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn range_members(values: &Vec<SourceDataRange>) -> Option<AtLeastTwo<DataRange>> {
    if values.len() < 2 {
        return None;
    }
    let first = match data_range(&values[0]) {
        Some(first) => first,
        None => return None,
    };
    let second = match data_range(&values[1]) {
        Some(second) => second,
        None => return None,
    };
    match range_rest_from(values, 2, Vec::new()) {
        Some(rest) => Some(AtLeastTwo {
            first,
            second,
            rest,
        }),
        None => None,
    }
}
fn data_property(source: &HeaderIri) -> DataProperty {
    DataProperty { iri: iri(source) }
}
/// The data number restriction of a bound.
fn data_cardinality(
    bound: Bound,
    value: Natural,
    property: DataProperty,
    range: Option<DataRange>,
) -> ClassExpression {
    match bound {
        Bound::Min => ClassExpression::DataMinCardinality(value, property, range),
        Bound::Max => ClassExpression::DataMaxCardinality(value, property, range),
        Bound::Exact => ClassExpression::DataExactCardinality(value, property, range),
    }
}
/// The number `value`.
fn natural(value: usize) -> Natural {
    if value == 0 {
        Natural::Zero
    } else {
        Natural::Succ(Box::new(natural(value - 1)))
    }
}
/// The number restriction of a bound.
fn cardinality(
    bound: Bound,
    value: Natural,
    property: ObjectPropertyExpression,
    filler: Option<Box<ClassExpression>>,
) -> ClassExpression {
    match bound {
        Bound::Min => ClassExpression::ObjectMinCardinality(value, property, filler),
        Bound::Max => ClassExpression::ObjectMaxCardinality(value, property, filler),
        Bound::Exact => ClassExpression::ObjectExactCardinality(value, property, filler),
    }
}
fn class(source: &SourceClass, scope: &Vec<u8>) -> Option<ClassExpression> {
    match source {
        SourceClass::Named(name) => Some(ClassExpression::Class(Class { iri: iri(name) })),
        SourceClass::IntersectionOf { members, .. } => match members_of(members, scope) {
            Some(members) => Some(ClassExpression::ObjectIntersectionOf(Box::new(members))),
            None => None,
        },
        SourceClass::UnionOf { members, .. } => match members_of(members, scope) {
            Some(members) => Some(ClassExpression::ObjectUnionOf(Box::new(members))),
            None => None,
        },
        SourceClass::ComplementOf { operand, .. } => match class(operand, scope) {
            Some(operand) => Some(ClassExpression::ObjectComplementOf(Box::new(operand))),
            None => None,
        },
        SourceClass::OneOf { members, .. } => match enumeration(members, scope) {
            Some(members) => Some(ClassExpression::ObjectOneOf(members)),
            None => None,
        },
        SourceClass::SomeValuesFrom {
            property, filler, ..
        } => match class(filler, scope) {
            Some(filler) => Some(ClassExpression::ObjectSomeValuesFrom(
                self::property(property),
                Box::new(filler),
            )),
            None => None,
        },
        SourceClass::AllValuesFrom {
            property, filler, ..
        } => match class(filler, scope) {
            Some(filler) => Some(ClassExpression::ObjectAllValuesFrom(
                self::property(property),
                Box::new(filler),
            )),
            None => None,
        },
        SourceClass::HasValue {
            property,
            individual: value,
            ..
        } => Some(ClassExpression::ObjectHasValue(
            self::property(property),
            individual(value, scope),
        )),
        SourceClass::HasSelf { property, .. } => {
            Some(ClassExpression::ObjectHasSelf(self::property(property)))
        }
        SourceClass::Cardinality {
            bound,
            value,
            property,
            filler,
            ..
        } => match filler {
            Some(filler) => match class(filler, scope) {
                Some(filler) => Some(cardinality(
                    *bound,
                    natural(*value),
                    self::property(property),
                    Some(Box::new(filler)),
                )),
                None => None,
            },
            None => Some(cardinality(
                *bound,
                natural(*value),
                self::property(property),
                None,
            )),
        },
        SourceClass::DataSomeValuesFrom {
            property, range, ..
        } => match data_range(range) {
            Some(range) => Some(ClassExpression::DataSomeValuesFrom(
                data_property(property),
                range,
            )),
            None => None,
        },
        SourceClass::DataAllValuesFrom {
            property, range, ..
        } => match data_range(range) {
            Some(range) => Some(ClassExpression::DataAllValuesFrom(
                data_property(property),
                range,
            )),
            None => None,
        },
        SourceClass::DataHasValue {
            property, value, ..
        } => Some(ClassExpression::DataHasValue(
            data_property(property),
            literal(value),
        )),
        SourceClass::DataCardinality {
            bound,
            value,
            property,
            range,
            ..
        } => match range {
            Some(range) => match data_range(range) {
                Some(range) => Some(data_cardinality(
                    *bound,
                    natural(*value),
                    data_property(property),
                    Some(range),
                )),
                None => None,
            },
            None => Some(data_cardinality(
                *bound,
                natural(*value),
                data_property(property),
                None,
            )),
        },
    }
}
fn rest_from(
    values: &Vec<SourceClass>,
    index: usize,
    mut out: Vec<ClassExpression>,
    scope: &Vec<u8>,
) -> Option<Vec<ClassExpression>> {
    if index < values.len() {
        match class(&values[index], scope) {
            Some(value) => {
                out.push(value);
                rest_from(values, index + 1, out, scope)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn members_of(values: &Vec<SourceClass>, scope: &Vec<u8>) -> Option<AtLeastTwo<ClassExpression>> {
    if values.len() < 2 {
        return None;
    }
    let first = match class(&values[0], scope) {
        Some(first) => first,
        None => return None,
    };
    let second = match class(&values[1], scope) {
        Some(second) => second,
        None => return None,
    };
    match rest_from(values, 2, Vec::new(), scope) {
        Some(rest) => Some(AtLeastTwo {
            first,
            second,
            rest,
        }),
        None => None,
    }
}
fn entity(source: &SourceEntity) -> Entity {
    let name = iri(&source.iri);
    match source.kind {
        SourceEntityKind::Class => Entity::Class(Class { iri: name }),
        SourceEntityKind::Datatype => Entity::Datatype(Datatype { iri: name }),
        SourceEntityKind::ObjectProperty => Entity::ObjectProperty(ObjectProperty { iri: name }),
        SourceEntityKind::DataProperty => Entity::DataProperty(DataProperty { iri: name }),
        SourceEntityKind::AnnotationProperty => {
            Entity::AnnotationProperty(AnnotationProperty { iri: name })
        }
        SourceEntityKind::NamedIndividual => Entity::NamedIndividual(NamedIndividual { iri: name }),
    }
}
fn subject(source: &SourceAnnotationSubject, scope: &Vec<u8>) -> AnnotationSubject {
    match source {
        SourceAnnotationSubject::Iri(value) => AnnotationSubject::Iri(iri(value)),
        SourceAnnotationSubject::Anonymous { label, .. } => {
            AnnotationSubject::Anonymous(anonymous(label, scope))
        }
    }
}
fn annotation_axiom(source: &SourceAnnotationAxiomBody, scope: &Vec<u8>) -> Axiom {
    match source {
        SourceAnnotationAxiomBody::Assertion {
            property,
            subject,
            value,
        } => Axiom::AnnotationAssertion(
            AnnotationProperty { iri: iri(property) },
            self::subject(subject, scope),
            annotation_value(value, scope),
        ),
        SourceAnnotationAxiomBody::SubProperty {
            sub_property,
            super_property,
        } => Axiom::SubAnnotationPropertyOf(
            AnnotationProperty {
                iri: iri(sub_property),
            },
            AnnotationProperty {
                iri: iri(super_property),
            },
        ),
        SourceAnnotationAxiomBody::Domain { property, domain } => {
            Axiom::AnnotationPropertyDomain(AnnotationProperty { iri: iri(property) }, iri(domain))
        }
        SourceAnnotationAxiomBody::Range { property, range } => {
            Axiom::AnnotationPropertyRange(AnnotationProperty { iri: iri(property) }, iri(range))
        }
    }
}
fn class_axiom(source: &SourceClassAxiomBody, scope: &Vec<u8>) -> Option<Axiom> {
    match source {
        SourceClassAxiomBody::SubClassOf { sub, sup } => {
            let sub = match class(sub, scope) {
                Some(sub) => sub,
                None => return None,
            };
            match class(sup, scope) {
                Some(sup) => Some(Axiom::SubClassOf(sub, sup)),
                None => None,
            }
        }
        SourceClassAxiomBody::EquivalentClasses(members) => match members_of(members, scope) {
            Some(members) => Some(Axiom::EquivalentClasses(members)),
            None => None,
        },
        SourceClassAxiomBody::DisjointClasses(members) => match members_of(members, scope) {
            Some(members) => Some(Axiom::DisjointClasses(members)),
            None => None,
        },
        SourceClassAxiomBody::DisjointUnion {
            class: name,
            members,
        } => match members_of(members, scope) {
            Some(members) => Some(Axiom::DisjointUnion(Class { iri: iri(name) }, members)),
            None => None,
        },
        SourceClassAxiomBody::ObjectPropertyDomain { property, domain } => {
            match class(domain, scope) {
                Some(domain) => Some(Axiom::ObjectPropertyDomain(
                    self::property(property),
                    domain,
                )),
                None => None,
            }
        }
        SourceClassAxiomBody::ObjectPropertyRange { property, range } => {
            match class(range, scope) {
                Some(range) => Some(Axiom::ObjectPropertyRange(self::property(property), range)),
                None => None,
            }
        }
    }
}
/// The model of `values[index..]` after `out`.
fn properties_from(
    values: &Vec<SourceObjectProperty>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Vec<ObjectPropertyExpression> {
    if index < values.len() && out.len() < values.len() {
        out.push(property(&values[index]));
        properties_from(values, index + 1, out)
    } else {
        out
    }
}
/// A member list of at least two object property expressions.
fn property_members(
    values: &Vec<SourceObjectProperty>,
) -> Option<AtLeastTwo<ObjectPropertyExpression>> {
    if values.len() < 2 {
        return None;
    }
    Some(AtLeastTwo {
        first: property(&values[0]),
        second: property(&values[1]),
        rest: properties_from(values, 2, Vec::new()),
    })
}
fn sub_property(source: &SourceSubProperty) -> Option<SubObjectPropertyExpression> {
    match source {
        SourceSubProperty::Single(value) => {
            Some(SubObjectPropertyExpression::Single(property(value)))
        }
        SourceSubProperty::Chain { members, .. } => match property_members(members) {
            Some(members) => Some(SubObjectPropertyExpression::Chain(members)),
            None => None,
        },
    }
}
fn characteristic_axiom(
    characteristic: PropertyCharacteristic,
    value: ObjectPropertyExpression,
) -> Axiom {
    match characteristic {
        PropertyCharacteristic::Functional => Axiom::FunctionalObjectProperty(value),
        PropertyCharacteristic::InverseFunctional => Axiom::InverseFunctionalObjectProperty(value),
        PropertyCharacteristic::Reflexive => Axiom::ReflexiveObjectProperty(value),
        PropertyCharacteristic::Irreflexive => Axiom::IrreflexiveObjectProperty(value),
        PropertyCharacteristic::Symmetric => Axiom::SymmetricObjectProperty(value),
        PropertyCharacteristic::Asymmetric => Axiom::AsymmetricObjectProperty(value),
        PropertyCharacteristic::Transitive => Axiom::TransitiveObjectProperty(value),
    }
}
fn property_axiom(source: &SourcePropertyAxiomBody) -> Option<Axiom> {
    match source {
        SourcePropertyAxiomBody::SubObjectPropertyOf { sub, sup } => match sub_property(sub) {
            Some(sub) => Some(Axiom::SubObjectPropertyOf(sub, property(sup))),
            None => None,
        },
        SourcePropertyAxiomBody::EquivalentObjectProperties(members) => {
            match property_members(members) {
                Some(members) => Some(Axiom::EquivalentObjectProperties(members)),
                None => None,
            }
        }
        SourcePropertyAxiomBody::DisjointObjectProperties(members) => {
            match property_members(members) {
                Some(members) => Some(Axiom::DisjointObjectProperties(members)),
                None => None,
            }
        }
        SourcePropertyAxiomBody::InverseObjectProperties { first, second } => Some(
            Axiom::InverseObjectProperties(property(first), property(second)),
        ),
        SourcePropertyAxiomBody::Characteristic {
            characteristic,
            property: value,
        } => Some(characteristic_axiom(*characteristic, property(value))),
    }
}
fn assertion(source: &SourceAssertionBody, scope: &Vec<u8>) -> Option<Axiom> {
    match source {
        SourceAssertionBody::SameIndividual(members) => match individual_members(members, scope) {
            Some(members) => Some(Axiom::SameIndividual(members)),
            None => None,
        },
        SourceAssertionBody::DifferentIndividuals(members) => {
            match individual_members(members, scope) {
                Some(members) => Some(Axiom::DifferentIndividuals(members)),
                None => None,
            }
        }
        SourceAssertionBody::ClassAssertion {
            class: expression,
            individual: member,
        } => match class(expression, scope) {
            Some(expression) => Some(Axiom::ClassAssertion(expression, individual(member, scope))),
            None => None,
        },
        SourceAssertionBody::ObjectPropertyAssertion {
            property: role,
            source,
            target,
        } => Some(Axiom::ObjectPropertyAssertion(
            property(role),
            individual(source, scope),
            individual(target, scope),
        )),
        SourceAssertionBody::NegativeObjectPropertyAssertion {
            property: role,
            source,
            target,
        } => Some(Axiom::NegativeObjectPropertyAssertion(
            property(role),
            individual(source, scope),
            individual(target, scope),
        )),
    }
}
fn axiom(source: &SourceAxiom, scope: &Vec<u8>) -> Option<AnnotatedAxiom> {
    match source {
        SourceAxiom::Declaration(declaration) => Some(AnnotatedAxiom {
            annotations: annotations_from(&declaration.annotations, 0, Vec::new(), scope),
            axiom: Axiom::Declaration(entity(&declaration.entity)),
        }),
        SourceAxiom::Annotation(record) => Some(AnnotatedAxiom {
            annotations: annotations_from(&record.annotations, 0, Vec::new(), scope),
            axiom: annotation_axiom(&record.body, scope),
        }),
        SourceAxiom::Class(record) => match class_axiom(&record.body, scope) {
            Some(axiom) => Some(AnnotatedAxiom {
                annotations: annotations_from(&record.annotations, 0, Vec::new(), scope),
                axiom,
            }),
            None => None,
        },
        SourceAxiom::Property(record) => match property_axiom(&record.body) {
            Some(axiom) => Some(AnnotatedAxiom {
                annotations: annotations_from(&record.annotations, 0, Vec::new(), scope),
                axiom,
            }),
            None => None,
        },
        SourceAxiom::Assertion(record) => match assertion(&record.body, scope) {
            Some(axiom) => Some(AnnotatedAxiom {
                annotations: annotations_from(&record.annotations, 0, Vec::new(), scope),
                axiom,
            }),
            None => None,
        },
    }
}
fn axioms_from(
    values: &Vec<SourceAxiom>,
    index: usize,
    mut out: Vec<AnnotatedAxiom>,
    scope: &Vec<u8>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < values.len() {
        match axiom(&values[index], scope) {
            Some(value) => {
                out.push(value);
                axioms_from(values, index + 1, out, scope)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn imports_from(values: &Vec<ImportReference>, index: usize, mut out: Vec<Iri>) -> Vec<Iri> {
    if index < values.len() {
        out.push(iri(&values[index].target));
        imports_from(values, index + 1, out)
    } else {
        out
    }
}
fn identity(source: &SourceOntologyIdentity) -> OntologyIdentity {
    match source {
        SourceOntologyIdentity::Anonymous => OntologyIdentity::Anonymous,
        SourceOntologyIdentity::Named { ontology, version } => OntologyIdentity::Named {
            ontology: iri(ontology),
            version: match version {
                Some(version) => Some(iri(version)),
                None => None,
            },
        },
    }
}
/// The raw OWL ontology of a read document: its identity, imports, ontology
/// annotations and axioms with their annotations, in source order. Node IDs
/// become anonymous individuals in `scope`.
pub fn document_ontology(document: &SourceDocument, scope: &Vec<u8>) -> Option<RawOntology> {
    match axioms_from(&document.tail.axioms, 0, Vec::new(), scope) {
        Some(axioms) => Some(RawOntology {
            identity: identity(&document.tail.identity),
            imports: imports_from(&document.tail.imports, 0, Vec::new()),
            annotations: annotations_from(&document.tail.annotations, 0, Vec::new(), scope),
            axioms,
        }),
        None => None,
    }
}
