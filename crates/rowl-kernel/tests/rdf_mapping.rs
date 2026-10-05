use rowl_kernel::data_ontology::{
    prepare, prepared_consistent, prepared_instance_of, prepared_subsumed,
};
use rowl_kernel::model::*;
use rowl_kernel::ntriples::{read, ReadResult};
use rowl_kernel::probes::Natural;
use rowl_kernel::rdf::RawGraph;
use rowl_kernel::rdf_mapping::map_graph;

const MEDICATION: &[u8] = include_bytes!("../../../examples/medication-safety.nt");
const EX: &str = "https://example.org/medication/";

fn graph(source: &[u8]) -> RawGraph {
    match read(&source.to_vec(), &b"test".to_vec()) {
        ReadResult::Graph(graph) => graph,
        ReadResult::Error(error) => panic!("N-Triples error at {}", error.offset),
    }
}

fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: Iri {
            spelling: format!("{EX}{name}").into_bytes(),
        },
    })
}

fn individual(name: &str) -> NamedIndividual {
    NamedIndividual {
        iri: Iri {
            spelling: format!("{EX}{name}").into_bytes(),
        },
    }
}

#[test]
fn the_medication_graph_maps_to_its_ontology_and_answers_alike() {
    let mapped = map_graph(&graph(MEDICATION)).expect("the graph is the image of an ontology");
    let ontology = &mapped.ontology;
    match &ontology.identity {
        OntologyIdentity::Named { ontology, version } => {
            assert_eq!(ontology.spelling, format!("{EX}records").into_bytes());
            assert!(version.is_none());
        }
        OntologyIdentity::Anonymous => panic!("the header names the ontology"),
    }
    assert_eq!(ontology.annotations.len(), 2);
    // 16 declarations and 14 further axioms.
    assert_eq!(ontology.axioms.len(), 30);
    // Blank nodes: the intersection, its two list cells, its two restrictions
    // and the nested one, and the four class assertion restrictions.
    assert_eq!(mapped.blanks.len(), 10);
    let prepared = prepare(&ontology.axioms).expect("the axioms are in the supported fragment");
    assert_eq!(prepared_consistent(&prepared), Some(true));
    for (patient, expected) in [("alice", true), ("bob", false), ("carol", false)] {
        assert_eq!(
            prepared_instance_of(&prepared, &individual(patient), &class("AllergyAlert")),
            Some(expected)
        );
    }
    assert_eq!(
        prepared_subsumed(&prepared, &class("Amoxicillin"), &class("Penicillin")),
        Some(true)
    );
}

#[test]
fn graphs_outside_the_image_are_refused() {
    // An undeclared property has no type.
    let undeclared = b"<urn:a> <urn:p> <urn:b> .\n";
    assert!(map_graph(&graph(undeclared)).is_none());
    // A restriction without a property is no class expression.
    let incomplete = b"<urn:a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> _:r .\n\
        _:r <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Restriction> .\n";
    assert!(map_graph(&graph(incomplete)).is_none());
    // A triple left over is refused.
    let leftover = b"<urn:C> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .\n\
        _:x <http://www.w3.org/2002/07/owl#onProperty> <urn:p> .\n";
    assert!(map_graph(&graph(leftover)).is_none());
    // A blank class expression shared by two axioms is no image.
    let shared = b"<urn:p> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#ObjectProperty> .\n\
        _:r <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Restriction> .\n\
        _:r <http://www.w3.org/2002/07/owl#onProperty> <urn:p> .\n\
        _:r <http://www.w3.org/2002/07/owl#someValuesFrom> <urn:B> .\n\
        _:r <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:C> .\n\
        _:r <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:D> .\n";
    assert!(map_graph(&graph(shared)).is_none());
}

#[test]
fn every_construct_of_the_mapping_is_read() {
    let source = b"<urn:o> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Ontology> .\n\
        <urn:o> <http://www.w3.org/2002/07/owl#versionIRI> <urn:o1> .\n\
        <urn:o> <http://www.w3.org/2002/07/owl#imports> <urn:other> .\n\
        <urn:p> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#ObjectProperty> .\n\
        <urn:q> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#ObjectProperty> .\n\
        <urn:d> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#DatatypeProperty> .\n\
        <urn:e> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#DatatypeProperty> .\n\
        <urn:A> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .\n\
        <urn:p> <http://www.w3.org/2002/07/owl#inverseOf> <urn:q> .\n\
        <urn:p> <http://www.w3.org/2002/07/owl#propertyChainAxiom> _:c1 .\n\
        _:c1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> <urn:q> .\n\
        _:c1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:c2 .\n\
        _:c2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:inv .\n\
        _:c2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .\n\
        _:inv <http://www.w3.org/2002/07/owl#inverseOf> <urn:p> .\n\
        <urn:d> <http://www.w3.org/2000/01/rdf-schema#range> _:dr .\n\
        _:dr <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2000/01/rdf-schema#Datatype> .\n\
        _:dr <http://www.w3.org/2002/07/owl#onDatatype> <http://www.w3.org/2001/XMLSchema#integer> .\n\
        _:dr <http://www.w3.org/2002/07/owl#withRestrictions> _:f1 .\n\
        _:f1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:facet .\n\
        _:f1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .\n\
        _:facet <http://www.w3.org/2001/XMLSchema#minInclusive> \"18\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n\
        <urn:A> <http://www.w3.org/2002/07/owl#equivalentClass> _:card .\n\
        _:card <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Restriction> .\n\
        _:card <http://www.w3.org/2002/07/owl#onProperty> <urn:d> .\n\
        _:card <http://www.w3.org/2002/07/owl#minQualifiedCardinality> \"2\"^^<http://www.w3.org/2001/XMLSchema#nonNegativeInteger> .\n\
        _:card <http://www.w3.org/2002/07/owl#onDataRange> <http://www.w3.org/2001/XMLSchema#string> .\n\
        _:all <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#AllDifferent> .\n\
        _:all <http://www.w3.org/2002/07/owl#members> _:m1 .\n\
        _:m1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> <urn:a> .\n\
        _:m1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:m2 .\n\
        _:m2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> <urn:b> .\n\
        _:m2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:m3 .\n\
        _:m3 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:anon .\n\
        _:m3 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .\n\
        _:neg <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#NegativePropertyAssertion> .\n\
        _:neg <http://www.w3.org/2002/07/owl#sourceIndividual> <urn:a> .\n\
        _:neg <http://www.w3.org/2002/07/owl#assertionProperty> <urn:e> .\n\
        _:neg <http://www.w3.org/2002/07/owl#targetValue> \"x\"@en .\n\
        <urn:a> <urn:d> \"7\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n\
        <urn:a> <http://www.w3.org/2000/01/rdf-schema#label> \"An A\"@en .\n\
        <urn:A> <http://www.w3.org/2000/01/rdf-schema#comment> \"plain\" .\n";
    let mapped = map_graph(&graph(source)).expect("every construct is read");
    let axioms = &mapped.ontology.axioms;
    let mut kinds = Vec::new();
    for item in axioms {
        kinds.push(match &item.axiom {
            Axiom::Declaration(_) => "declaration",
            Axiom::InverseObjectProperties(_, _) => "inverse",
            Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(chain), _) => {
                assert!(matches!(chain.second, ObjectPropertyExpression::Inverse(_)));
                "chain"
            }
            Axiom::DataPropertyRange(_, DataRange::Restriction(_, facets)) => {
                assert_eq!(facets.first.value.lexical, b"18".to_vec());
                "range"
            }
            Axiom::EquivalentClasses(members) => {
                assert!(matches!(
                    members.second,
                    ClassExpression::DataMinCardinality(Natural::Succ(_), _, Some(_))
                ));
                "equivalent"
            }
            Axiom::DifferentIndividuals(members) => {
                assert_eq!(members.rest.len(), 1);
                "different"
            }
            Axiom::NegativeDataPropertyAssertion(_, _, value) => {
                assert_eq!(value.lexical, b"x@en".to_vec());
                "negative"
            }
            Axiom::DataPropertyAssertion(_, _, _) => "data",
            Axiom::AnnotationAssertion(_, _, _) => "annotation",
            _ => "other",
        });
    }
    assert_eq!(
        kinds,
        vec![
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "inverse",
            "chain",
            "range",
            "equivalent",
            "different",
            "negative",
            "data",
            "annotation",
            "annotation",
        ]
    );
    // The chain's two cells and inverse, the range, its cell and facet node,
    // the cardinality, the AllDifferent node and its three cells, the negative
    // assertion node.
    assert_eq!(mapped.blanks.len(), 12);
    assert_eq!(mapped.ontology.imports.len(), 1);
}
