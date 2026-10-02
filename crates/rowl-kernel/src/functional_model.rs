//! The kernel's raw OWL model of a read Functional Syntax document.
//!
//! Every source record maps to the structural model with its exact IRI and
//! literal bytes; node IDs become anonymous individuals in the caller's scope,
//! and original tokens are dropped. The mapping fails only on a member list
//! with fewer than two members, which the proved document reader never
//! produces.
#![allow(clippy::ptr_arg, clippy::question_mark, clippy::manual_map)] // Explicit branches for the pinned extraction subset.
use crate::functional_annotation_axioms::{SourceAnnotationAxiomBody, SourceAnnotationSubject};
use crate::functional_annotations::{SourceAnnotation, SourceAnnotationValue};
use crate::functional_assertions::{SourceAssertionBody, SourceIndividual};
use crate::functional_class_axioms::SourceClassAxiomBody;
use crate::functional_classes::{SourceClass, SourceObjectProperty};
use crate::functional_declarations::{SourceEntity, SourceEntityKind};
use crate::functional_document::{SourceAxiom, SourceDocument};
use crate::functional_header::{HeaderIri, ImportReference, SourceOntologyIdentity};
use crate::functional_literals::SourceLiteral;
use crate::functional_property_axioms::{
    PropertyCharacteristic, SourcePropertyAxiomBody, SourceSubProperty,
};
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationProperty, AnnotationSubject, AnnotationValue,
    AnonymousIndividual, AtLeastTwo, Axiom, Class, ClassExpression, DataProperty, Datatype, Entity,
    Individual, Iri, Literal, NamedIndividual, ObjectProperty, ObjectPropertyExpression,
    OntologyIdentity, RawOntology, SubObjectPropertyExpression,
};

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
fn class(source: &SourceClass) -> Option<ClassExpression> {
    match source {
        SourceClass::Named(name) => Some(ClassExpression::Class(Class { iri: iri(name) })),
        SourceClass::IntersectionOf { members, .. } => match members_of(members) {
            Some(members) => Some(ClassExpression::ObjectIntersectionOf(Box::new(members))),
            None => None,
        },
        SourceClass::UnionOf { members, .. } => match members_of(members) {
            Some(members) => Some(ClassExpression::ObjectUnionOf(Box::new(members))),
            None => None,
        },
        SourceClass::ComplementOf { operand, .. } => match class(operand) {
            Some(operand) => Some(ClassExpression::ObjectComplementOf(Box::new(operand))),
            None => None,
        },
        SourceClass::SomeValuesFrom {
            property, filler, ..
        } => match class(filler) {
            Some(filler) => Some(ClassExpression::ObjectSomeValuesFrom(
                self::property(property),
                Box::new(filler),
            )),
            None => None,
        },
        SourceClass::AllValuesFrom {
            property, filler, ..
        } => match class(filler) {
            Some(filler) => Some(ClassExpression::ObjectAllValuesFrom(
                self::property(property),
                Box::new(filler),
            )),
            None => None,
        },
    }
}
fn rest_from(
    values: &Vec<SourceClass>,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < values.len() {
        match class(&values[index]) {
            Some(value) => {
                out.push(value);
                rest_from(values, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn members_of(values: &Vec<SourceClass>) -> Option<AtLeastTwo<ClassExpression>> {
    if values.len() < 2 {
        return None;
    }
    let first = match class(&values[0]) {
        Some(first) => first,
        None => return None,
    };
    let second = match class(&values[1]) {
        Some(second) => second,
        None => return None,
    };
    match rest_from(values, 2, Vec::new()) {
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
fn class_axiom(source: &SourceClassAxiomBody) -> Option<Axiom> {
    match source {
        SourceClassAxiomBody::SubClassOf { sub, sup } => {
            let sub = match class(sub) {
                Some(sub) => sub,
                None => return None,
            };
            match class(sup) {
                Some(sup) => Some(Axiom::SubClassOf(sub, sup)),
                None => None,
            }
        }
        SourceClassAxiomBody::EquivalentClasses(members) => match members_of(members) {
            Some(members) => Some(Axiom::EquivalentClasses(members)),
            None => None,
        },
        SourceClassAxiomBody::DisjointClasses(members) => match members_of(members) {
            Some(members) => Some(Axiom::DisjointClasses(members)),
            None => None,
        },
        SourceClassAxiomBody::DisjointUnion {
            class: name,
            members,
        } => match members_of(members) {
            Some(members) => Some(Axiom::DisjointUnion(Class { iri: iri(name) }, members)),
            None => None,
        },
        SourceClassAxiomBody::ObjectPropertyDomain { property, domain } => match class(domain) {
            Some(domain) => Some(Axiom::ObjectPropertyDomain(
                self::property(property),
                domain,
            )),
            None => None,
        },
        SourceClassAxiomBody::ObjectPropertyRange { property, range } => match class(range) {
            Some(range) => Some(Axiom::ObjectPropertyRange(self::property(property), range)),
            None => None,
        },
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
fn individual(source: &SourceIndividual, scope: &Vec<u8>) -> Individual {
    match source {
        SourceIndividual::Named(name) => Individual::Named(NamedIndividual { iri: iri(name) }),
        SourceIndividual::Anonymous { label, .. } => Individual::Anonymous(anonymous(label, scope)),
    }
}
fn assertion(source: &SourceAssertionBody, scope: &Vec<u8>) -> Option<Axiom> {
    match source {
        SourceAssertionBody::ClassAssertion {
            class: expression,
            individual: member,
        } => match class(expression) {
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
        SourceAxiom::Class(record) => match class_axiom(&record.body) {
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
