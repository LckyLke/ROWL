use rowl_kernel::axiom_equality::{same_axiom, same_body};
use rowl_kernel::data_ontology::{
    prepare, prepared_consistent, prepared_instance_of, prepared_subsumed,
};
use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{read_document, DocumentLimits};
use rowl_kernel::functional_model::document_ontology;
use rowl_kernel::model::*;
use rowl_kernel::ntriples::{read, ReadResult};
use rowl_kernel::probes::Natural;
use rowl_kernel::rdf::RawGraph;
use rowl_kernel::rdf_mapping::map_graph;

const MEDICATION: &[u8] = include_bytes!("../../../examples/medication-safety.nt");
const ANNOTATED_MEDICATION: &[u8] =
    include_bytes!("../../../examples/medication-safety-annotated.nt");
const DOSING: &[u8] = include_bytes!("data/dosing.nt");
const DOSING_FUNCTIONAL: &[u8] = include_bytes!("data/dosing.ofn");
const DOSING_ANNOTATED: &[u8] = include_bytes!("data/dosing-annotated.nt");
const DOSING_ANNOTATED_FUNCTIONAL: &[u8] = include_bytes!("data/dosing-annotated.ofn");
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

/// Runs `body` on a thread with a large stack: the readers recurse over the
/// triples of the graph.
fn on_large_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(body)
        .expect("thread")
        .join()
        .expect("no panic");
}

#[test]
fn scattered_blank_nodes_of_a_large_graph_are_read() {
    on_large_stack(|| {
        // Every class is below a restriction on p with the next class. The
        // four triples of each restriction are far apart: first every typing,
        // then every property, every filler and every subclass triple, the
        // property triples in reverse order.
        let count = 1000;
        let rdf_type = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>";
        let owl = "http://www.w3.org/2002/07/owl#";
        let mut lines = Vec::new();
        for i in 0..=count {
            lines.push(format!("<urn:C{i}> {rdf_type} <{owl}Class> ."));
        }
        for i in 0..count {
            lines.push(format!("_:r{i} {rdf_type} <{owl}Restriction> ."));
        }
        for i in (0..count).rev() {
            lines.push(format!("_:r{i} <{owl}onProperty> <urn:p> ."));
        }
        for i in 0..count {
            lines.push(format!("_:r{i} <{owl}someValuesFrom> <urn:C{}> .", i + 1));
        }
        for i in 0..count {
            lines.push(format!(
                "<urn:C{i}> <http://www.w3.org/2000/01/rdf-schema#subClassOf> _:r{i} ."
            ));
        }
        lines.push(format!("<urn:p> {rdf_type} <{owl}ObjectProperty> ."));
        let source = lines.join("\n") + "\n";
        let mapped = map_graph(&graph(source.as_bytes())).expect("the graph is read");
        let axioms = &mapped.ontology.axioms;
        assert_eq!(axioms.len(), (count + 2) + count);
        assert_eq!(mapped.blanks.len(), count);
        let mut subclasses = 0;
        for item in axioms {
            if let Axiom::SubClassOf(ClassExpression::Class(sub), sup) = &item.axiom {
                let index: usize = String::from_utf8(sub.iri.spelling[5..].to_vec())
                    .expect("utf-8")
                    .parse()
                    .expect("a number");
                match sup {
                    ClassExpression::ObjectSomeValuesFrom(
                        ObjectPropertyExpression::Property(property),
                        filler,
                    ) => {
                        assert_eq!(property.iri.spelling, b"urn:p".to_vec());
                        assert!(matches!(
                            filler.as_ref(),
                            ClassExpression::Class(next)
                                if next.iri.spelling == format!("urn:C{}", index + 1).into_bytes()
                        ));
                    }
                    _ => panic!("a restriction"),
                }
                assert_eq!(
                    mapped.blanks[subclasses].label,
                    format!("r{index}").into_bytes()
                );
                subclasses += 1;
            }
        }
        assert_eq!(subclasses, count);
    });
}

const RDFS_COMMENT: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#comment";
const RDFS_LABEL: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#label";

#[test]
fn the_annotated_medication_graph_keeps_its_axiom_annotations() {
    let mapped =
        map_graph(&graph(ANNOTATED_MEDICATION)).expect("the graph is the image of an ontology");
    let ontology = &mapped.ontology;
    assert_eq!(ontology.annotations.len(), 2);
    assert_eq!(ontology.axioms.len(), 30);
    // The ten blank nodes of the expressions and the two reifications.
    assert_eq!(mapped.blanks.len(), 12);
    let annotated: Vec<&AnnotatedAxiom> = ontology
        .axioms
        .iter()
        .filter(|item| !item.annotations.is_empty())
        .collect();
    assert_eq!(annotated.len(), 2);
    assert!(matches!(
        annotated[0].axiom,
        Axiom::TransitiveObjectProperty(_)
    ));
    assert!(matches!(
        annotated[1].axiom,
        Axiom::SubClassOf(ClassExpression::ObjectIntersectionOf(_), _)
    ));
    for item in annotated {
        assert_eq!(item.annotations.len(), 1);
        assert_eq!(
            item.annotations[0].property.iri.spelling,
            RDFS_COMMENT.to_vec()
        );
        assert!(item.annotations[0].annotations.is_empty());
    }
    let prepared = prepare(&ontology.axioms).expect("the axioms are in the supported fragment");
    assert_eq!(prepared_consistent(&prepared), Some(true));
    for (patient, expected) in [("alice", true), ("bob", false), ("carol", false)] {
        assert_eq!(
            prepared_instance_of(&prepared, &individual(patient), &class("AllergyAlert")),
            Some(expected)
        );
    }
}

fn literal_value(value: &AnnotationValue) -> Vec<u8> {
    match value {
        AnnotationValue::Literal(literal) => literal.lexical.clone(),
        _ => panic!("a literal"),
    }
}

#[test]
fn annotations_of_axioms_and_annotations_are_read() {
    let rdf = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
    let rdfs = "http://www.w3.org/2000/01/rdf-schema#";
    let owl = "http://www.w3.org/2002/07/owl#";
    let reify = |node: &str, kind: &str, source: &str, property: &str, target: &str| {
        format!(
            "{node} <{rdf}type> <{owl}{kind}> .\n\
             {node} <{owl}annotatedSource> {source} .\n\
             {node} <{owl}annotatedProperty> <{property}> .\n\
             {node} <{owl}annotatedTarget> {target} .\n"
        )
    };
    let mut source = String::new();
    // An ontology annotation with an annotation of its own.
    source += &format!("<urn:o> <{rdf}type> <{owl}Ontology> .\n");
    source += &format!("<urn:o> <{rdfs}label> \"O\" .\n");
    source += &reify(
        "_:w0",
        "Annotation",
        "<urn:o>",
        &format!("{rdfs}label"),
        "\"O\"",
    );
    source += &format!("_:w0 <{rdfs}comment> \"about the label\" .\n");
    // A reification before its main triple, with an annotated annotation.
    source += &reify(
        "_:x1",
        "Axiom",
        "<urn:A>",
        &format!("{rdfs}subClassOf"),
        "<urn:B>",
    );
    source += &format!("_:x1 <{rdfs}comment> \"As are Bs\" .\n");
    source += &reify(
        "_:w1",
        "Annotation",
        "_:x1",
        &format!("{rdfs}comment"),
        "\"As are Bs\"",
    );
    source += "_:w1 <urn:source> <urn:book> .\n";
    source += &format!("<urn:A> <{rdfs}subClassOf> <urn:B> .\n");
    for name in ["A", "B", "C"] {
        source += &format!("<urn:{name}> <{rdf}type> <{owl}Class> .\n");
    }
    source += &format!("<urn:p> <{rdf}type> <{owl}ObjectProperty> .\n");
    source += &format!("<urn:source> <{rdf}type> <{owl}AnnotationProperty> .\n");
    // An annotated declaration.
    source += &format!("<urn:D> <{rdf}type> <{owl}Class> .\n");
    source += &reify(
        "_:x2",
        "Axiom",
        "<urn:D>",
        &format!("{rdf}type"),
        &format!("<{owl}Class>"),
    );
    source += &format!("_:x2 <{rdfs}label> \"D\" .\n_:x2 <{rdfs}comment> \"declared\" .\n");
    // An annotated subclass axiom whose source is a blank node.
    source += &format!("_:r <{rdf}type> <{owl}Restriction> .\n");
    source += &format!("_:r <{owl}onProperty> <urn:p> .\n_:r <{owl}someValuesFrom> <urn:C> .\n");
    source += &format!("_:r <{rdfs}subClassOf> <urn:D> .\n");
    source += &reify(
        "_:x3",
        "Axiom",
        "_:r",
        &format!("{rdfs}subClassOf"),
        "<urn:D>",
    );
    source += &format!("_:x3 <{rdfs}label> \"restriction\" .\n");
    // An axiom represented by a blank node, its annotation first.
    source += &format!("_:d <{rdfs}comment> \"pairwise disjoint\" .\n");
    source += &format!("_:d <{rdf}type> <{owl}AllDisjointClasses> .\n_:d <{owl}members> _:m1 .\n");
    source += &format!("_:m1 <{rdf}first> <urn:A> .\n_:m1 <{rdf}rest> _:m2 .\n");
    source += &format!("_:m2 <{rdf}first> <urn:C> .\n_:m2 <{rdf}rest> _:m3 .\n");
    source += &format!("_:m3 <{rdf}first> <urn:D> .\n_:m3 <{rdf}rest> <{rdf}nil> .\n");
    source += &format!("_:n <{rdf}type> <{owl}NegativePropertyAssertion> .\n");
    source +=
        &format!("_:n <{owl}sourceIndividual> <urn:a> .\n_:n <{owl}assertionProperty> <urn:p> .\n");
    source += &format!("_:n <{owl}targetIndividual> <urn:b> .\n_:n <urn:source> \"observed\" .\n");
    // An annotated annotation assertion.
    source += &format!("<urn:a> <{rdfs}label> \"a\" .\n");
    source += &reify("_:x4", "Axiom", "<urn:a>", &format!("{rdfs}label"), "\"a\"");
    source += "_:x4 <urn:source> <urn:registry> .\n";

    let mapped = map_graph(&graph(source.as_bytes())).expect("every annotation is read");
    let ontology = &mapped.ontology;
    assert_eq!(ontology.annotations.len(), 1);
    assert_eq!(ontology.annotations[0].annotations.len(), 1);
    assert_eq!(
        literal_value(&ontology.annotations[0].annotations[0].value),
        b"about the label".to_vec()
    );
    let axioms = &ontology.axioms;
    assert_eq!(axioms.len(), 11);
    // SubClassOf(A B), its comment annotated with a source.
    assert!(matches!(axioms[0].axiom, Axiom::SubClassOf(_, _)));
    assert_eq!(axioms[0].annotations.len(), 1);
    assert_eq!(
        axioms[0].annotations[0].property.iri.spelling,
        RDFS_COMMENT.to_vec()
    );
    assert_eq!(axioms[0].annotations[0].annotations.len(), 1);
    assert_eq!(
        axioms[0].annotations[0].annotations[0]
            .property
            .iri
            .spelling,
        b"urn:source".to_vec()
    );
    // Five plain declarations, then the annotated one of D.
    for item in &axioms[1..6] {
        assert!(matches!(item.axiom, Axiom::Declaration(_)));
        assert!(item.annotations.is_empty());
    }
    assert!(matches!(
        axioms[6].axiom,
        Axiom::Declaration(Entity::Class(_))
    ));
    assert_eq!(axioms[6].annotations.len(), 2);
    assert_eq!(
        axioms[6].annotations[0].property.iri.spelling,
        RDFS_LABEL.to_vec()
    );
    assert!(matches!(
        axioms[7].axiom,
        Axiom::SubClassOf(ClassExpression::ObjectSomeValuesFrom(_, _), _)
    ));
    assert_eq!(
        literal_value(&axioms[7].annotations[0].value),
        b"restriction".to_vec()
    );
    assert!(matches!(&axioms[8].axiom, Axiom::DisjointClasses(members) if members.rest.len() == 1));
    assert_eq!(
        literal_value(&axioms[8].annotations[0].value),
        b"pairwise disjoint".to_vec()
    );
    assert!(matches!(
        axioms[9].axiom,
        Axiom::NegativeObjectPropertyAssertion(_, _, _)
    ));
    assert_eq!(
        literal_value(&axioms[9].annotations[0].value),
        b"observed".to_vec()
    );
    assert!(matches!(
        axioms[10].axiom,
        Axiom::AnnotationAssertion(_, _, _)
    ));
    assert_eq!(axioms[10].annotations.len(), 1);
    // The header's reification, then the blank nodes of the axioms in order.
    let labels: Vec<Vec<u8>> = mapped
        .blanks
        .iter()
        .map(|node| node.label.clone())
        .collect();
    let expected: Vec<Vec<u8>> = [
        "w0", "x1", "w1", "x2", "r", "x3", "d", "m1", "m2", "m3", "n", "x4",
    ]
    .iter()
    .map(|label| label.as_bytes().to_vec())
    .collect();
    assert_eq!(labels, expected);
}

#[test]
fn incomplete_or_foreign_reifications_are_refused() {
    let rdf = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
    let rdfs = "http://www.w3.org/2000/01/rdf-schema#";
    let owl = "http://www.w3.org/2002/07/owl#";
    let declarations =
        format!("<urn:A> <{rdf}type> <{owl}Class> .\n<urn:B> <{rdf}type> <{owl}Class> .\n");
    let main = format!("<urn:A> <{rdfs}subClassOf> <urn:B> .\n");
    let reification = |kind: &str, target: &str| {
        format!(
            "_:x <{rdf}type> <{owl}{kind}> .\n_:x <{owl}annotatedSource> <urn:A> .\n\
             _:x <{owl}annotatedProperty> <{rdfs}subClassOf> .\n_:x <{owl}annotatedTarget> {target} .\n"
        )
    };
    let comment = format!("_:x <{rdfs}comment> \"c\" .\n");
    // The plain graph and the annotated one are read.
    assert!(map_graph(&graph((declarations.clone() + &main).as_bytes())).is_some());
    let annotated = declarations.clone() + &main + &reification("Axiom", "<urn:B>") + &comment;
    assert!(map_graph(&graph(annotated.as_bytes())).is_some());
    // A reification without annotations is no image.
    let bare = declarations.clone() + &main + &reification("Axiom", "<urn:B>");
    assert!(map_graph(&graph(bare.as_bytes())).is_none());
    // A reification of a triple the graph lacks is left over.
    let other = declarations.clone() + &main + &reification("Axiom", "<urn:A>") + &comment;
    assert!(map_graph(&graph(other.as_bytes())).is_none());
    let missing = declarations.clone() + &reification("Axiom", "<urn:B>") + &comment;
    assert!(map_graph(&graph(missing.as_bytes())).is_none());
    // The forward mapping reifies an axiom with owl:Axiom, not owl:Annotation.
    let foreign = declarations.clone() + &main + &reification("Annotation", "<urn:B>") + &comment;
    assert!(map_graph(&graph(foreign.as_bytes())).is_none());
}

/// A class expression of the EL fragment: a named class `C{n}`, or an
/// existential restriction on the object property `r{n}`.
enum El {
    Named(usize),
    Some(usize, Box<El>),
}

/// The node, the triples in the order of the forward mapping, and the blank
/// nodes allocated, of an EL class expression.
fn el_triples(expression: &El, next: &mut usize) -> (String, Vec<String>, Vec<String>) {
    let rdf = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
    let owl = "http://www.w3.org/2002/07/owl#";
    match expression {
        El::Named(n) => (format!("<urn:el:C{n}>"), Vec::new(), Vec::new()),
        El::Some(role, filler) => {
            let label = format!("e{next}");
            *next += 1;
            let (node, rest, blanks) = el_triples(filler, next);
            let mut lines = vec![
                format!("_:{label} <{rdf}type> <{owl}Restriction> ."),
                format!("_:{label} <{owl}onProperty> <urn:el:r{role}> ."),
                format!("_:{label} <{owl}someValuesFrom> {node} ."),
            ];
            lines.extend(rest);
            let mut all = vec![label.clone()];
            all.extend(blanks);
            (format!("_:{label}"), lines, all)
        }
    }
}

fn is_el(expression: &ClassExpression, expected: &El) -> bool {
    match (expression, expected) {
        (ClassExpression::Class(class), El::Named(n)) => {
            class.iri.spelling == format!("urn:el:C{n}").into_bytes()
        }
        (
            ClassExpression::ObjectSomeValuesFrom(
                ObjectPropertyExpression::Property(property),
                filler,
            ),
            El::Some(role, inner),
        ) => {
            property.iri.spelling == format!("urn:el:r{role}").into_bytes() && is_el(filler, inner)
        }
        _ => false,
    }
}

#[test]
fn el_graphs_in_forward_order_read_back_exactly() {
    // The forward mapping of an EL ontology (the fragment of map_graph_complete):
    // its header, its declarations and its subclass axioms with the triples of
    // their restrictions, in that order, including a restriction on the left and
    // nested restrictions.
    let rdf = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
    let rdfs = "http://www.w3.org/2000/01/rdf-schema#";
    let owl = "http://www.w3.org/2002/07/owl#";
    let subclasses = vec![
        (El::Named(1), El::Named(0)),
        (El::Named(2), El::Some(0, Box::new(El::Named(3)))),
        (
            El::Some(1, Box::new(El::Some(0, Box::new(El::Named(4))))),
            El::Named(5),
        ),
        (
            El::Some(0, Box::new(El::Named(6))),
            El::Some(1, Box::new(El::Named(7))),
        ),
    ];
    let mut lines = vec![format!("<urn:el> <{rdf}type> <{owl}Ontology> .")];
    for n in 0..8 {
        lines.push(format!("<urn:el:C{n}> <{rdf}type> <{owl}Class> ."));
    }
    for role in 0..2 {
        lines.push(format!(
            "<urn:el:r{role}> <{rdf}type> <{owl}ObjectProperty> ."
        ));
    }
    let mut next = 0;
    let mut expected_blanks = Vec::new();
    for (sub, sup) in &subclasses {
        let (left, left_lines, left_blanks) = el_triples(sub, &mut next);
        let (right, right_lines, right_blanks) = el_triples(sup, &mut next);
        lines.push(format!("{left} <{rdfs}subClassOf> {right} ."));
        lines.extend(left_lines);
        lines.extend(right_lines);
        expected_blanks.extend(left_blanks);
        expected_blanks.extend(right_blanks);
    }
    let source = lines.join("\n") + "\n";
    let mapped =
        map_graph(&graph(source.as_bytes())).expect("the graph is the image of its ontology");
    let ontology = &mapped.ontology;
    match &ontology.identity {
        OntologyIdentity::Named { ontology, version } => {
            assert_eq!(ontology.spelling, b"urn:el".to_vec());
            assert!(version.is_none());
        }
        OntologyIdentity::Anonymous => panic!("the header names the ontology"),
    }
    assert!(ontology.imports.is_empty());
    assert!(ontology.annotations.is_empty());
    assert_eq!(ontology.axioms.len(), 8 + 2 + subclasses.len());
    for (index, item) in ontology.axioms.iter().enumerate() {
        assert!(item.annotations.is_empty());
        if index < 8 {
            assert!(
                matches!(&item.axiom, Axiom::Declaration(Entity::Class(class))
                if class.iri.spelling == format!("urn:el:C{index}").into_bytes())
            );
        } else if index < 10 {
            assert!(
                matches!(&item.axiom, Axiom::Declaration(Entity::ObjectProperty(property))
                if property.iri.spelling == format!("urn:el:r{}", index - 8).into_bytes())
            );
        } else {
            let (sub, sup) = &subclasses[index - 10];
            match &item.axiom {
                Axiom::SubClassOf(left, right) => assert!(is_el(left, sub) && is_el(right, sup)),
                _ => panic!("a subclass axiom"),
            }
        }
    }
    let labels: Vec<Vec<u8>> = mapped
        .blanks
        .iter()
        .map(|node| node.label.clone())
        .collect();
    let expected: Vec<Vec<u8>> = expected_blanks
        .iter()
        .map(|label| label.as_bytes().to_vec())
        .collect();
    assert_eq!(labels, expected);
}

/// The ontology of a Functional Syntax document, its anonymous individuals in
/// the scope `test` like the blank nodes of `graph`.
fn functional_ontology(source: &[u8]) -> RawOntology {
    let limits = DocumentLimits {
        tokens: 10_000,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 200,
        axioms: 200,
        annotations: AnnotationLimits {
            depth: 2,
            count: 10,
            iri: 200,
            lexical: 200,
        },
        classes: ClassLimits {
            depth: 10,
            count: 100,
            iri: 200,
        },
    };
    let document = match read_document(&source.to_vec(), &limits) {
        Ok(document) => document,
        Err(_) => panic!("the fixture is a Functional Syntax document"),
    };
    document_ontology(&document, &b"test".to_vec()).expect("every read document maps")
}

fn same_iri(left: &Iri, right: &Iri) -> bool {
    left.spelling == right.spelling
}

#[test]
fn readable_graphs_in_forward_order_read_back_exactly() {
    // The forward mapping of an ontology of the fragment of
    // RdfReadOntology.map_graph_complete, in order: a version IRI and an import,
    // every kind of class expression and data range, and every kind of axiom,
    // equivalences of two members and disjointness and difference of two and of
    // three, an anonymous individual and inverse properties in many positions.
    let expected = functional_ontology(DOSING_FUNCTIONAL);
    let mapped = map_graph(&graph(DOSING)).expect("the graph is the image of its ontology");
    let ontology = &mapped.ontology;
    match (&ontology.identity, &expected.identity) {
        (
            OntologyIdentity::Named { ontology, version },
            OntologyIdentity::Named {
                ontology: expected_ontology,
                version: expected_version,
            },
        ) => {
            assert!(same_iri(ontology, expected_ontology));
            match (version, expected_version) {
                (Some(version), Some(expected_version)) => {
                    assert!(same_iri(version, expected_version))
                }
                _ => panic!("both have a version IRI"),
            }
        }
        _ => panic!("both are named"),
    }
    assert_eq!(ontology.imports.len(), 1);
    assert!(same_iri(&ontology.imports[0], &expected.imports[0]));
    assert!(ontology.annotations.is_empty() && expected.annotations.is_empty());
    assert_eq!(ontology.axioms.len(), expected.axioms.len());
    assert_eq!(ontology.axioms.len(), 80);
    for (index, (read, written)) in ontology
        .axioms
        .iter()
        .zip(expected.axioms.iter())
        .enumerate()
    {
        assert!(same_axiom(read, written), "axiom {index} differs");
    }
    // The blank nodes in the order in which the forward mapping allocates them.
    let labels: Vec<Vec<u8>> = mapped
        .blanks
        .iter()
        .map(|node| node.label.clone())
        .collect();
    let allocated: Vec<Vec<u8>> = (1..=71).map(|n| format!("b{n}").into_bytes()).collect();
    assert_eq!(labels, allocated);
}

/// The lines of `source` in an order fixed by `seed` (a Fisher-Yates shuffle
/// driven by a 64-bit linear congruential generator).
fn shuffled_lines(source: &[u8], seed: u64) -> Vec<u8> {
    let mut lines: Vec<&[u8]> = source
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .collect();
    let mut state = seed;
    for last in (1..lines.len()).rev() {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let pick = ((state >> 33) as usize) % (last + 1);
        lines.swap(last, pick);
    }
    let mut out = Vec::new();
    for line in lines {
        out.extend_from_slice(line);
        out.push(b'\n');
    }
    out
}

/// Whether `read` lists the axioms of `written` in some order.
fn same_axioms_up_to_order(read: &[AnnotatedAxiom], written: &[AnnotatedAxiom]) -> bool {
    if read.len() != written.len() {
        return false;
    }
    let mut taken = vec![false; written.len()];
    read.iter().all(|axiom| {
        let found =
            (0..written.len()).find(|&index| !taken[index] && same_axiom(axiom, &written[index]));
        match found {
            Some(index) => {
                taken[index] = true;
                true
            }
            None => false,
        }
    })
}

#[test]
fn readable_graphs_in_any_order_read_back_up_to_order() {
    // RdfReadPermuted.map_graph_complete_perm: the triples of the forward
    // mapping of tests/data/dosing.ofn in reverse order and in shuffled orders
    // read back to the same ontology, its axioms and imports up to their order
    // and the same blank nodes up to their order.
    let expected = functional_ontology(DOSING_FUNCTIONAL);
    let mut reversed: Vec<&[u8]> = DOSING
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .collect();
    reversed.reverse();
    let mut backwards = reversed.join(&b'\n');
    backwards.push(b'\n');
    let mut sources = vec![backwards];
    for seed in [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233] {
        sources.push(shuffled_lines(DOSING, seed));
    }
    let mut allocated: Vec<Vec<u8>> = (1..=71).map(|n| format!("b{n}").into_bytes()).collect();
    allocated.sort();
    for (round, source) in sources.iter().enumerate() {
        assert_ne!(&source[..], DOSING, "round {round} reorders the triples");
        let mapped = map_graph(&graph(source))
            .unwrap_or_else(|| panic!("round {round}: the graph is the image of its ontology"));
        let ontology = &mapped.ontology;
        match (&ontology.identity, &expected.identity) {
            (
                OntologyIdentity::Named { ontology, version },
                OntologyIdentity::Named {
                    ontology: expected_ontology,
                    version: Some(expected_version),
                },
            ) => {
                assert!(same_iri(ontology, expected_ontology));
                assert!(matches!(version, Some(version) if same_iri(version, expected_version)));
            }
            _ => panic!("round {round}: both are named with a version IRI"),
        }
        assert_eq!(ontology.imports.len(), 1);
        assert!(same_iri(&ontology.imports[0], &expected.imports[0]));
        assert!(ontology.annotations.is_empty());
        assert!(
            same_axioms_up_to_order(&ontology.axioms, &expected.axioms),
            "round {round}: the same axioms"
        );
        let mut labels: Vec<Vec<u8>> = mapped
            .blanks
            .iter()
            .map(|node| node.label.clone())
            .collect();
        labels.sort();
        assert_eq!(labels, allocated, "round {round}: the same blank nodes");
    }
}

fn same_value(left: &AnnotationValue, right: &AnnotationValue) -> bool {
    match (left, right) {
        (AnnotationValue::Iri(left), AnnotationValue::Iri(right)) => same_iri(left, right),
        (AnnotationValue::Anonymous(left), AnnotationValue::Anonymous(right)) => {
            left.scope == right.scope && left.label == right.label
        }
        (AnnotationValue::Literal(left), AnnotationValue::Literal(right)) => {
            left.lexical == right.lexical && same_iri(&left.datatype.iri, &right.datatype.iri)
        }
        _ => false,
    }
}

/// Whether two lists of annotations are the same, in the same order.
fn same_annotations_in_order(left: &[Annotation], right: &[Annotation]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right.iter()).all(|(left, right)| {
            same_iri(&left.property.iri, &right.property.iri)
                && same_value(&left.value, &right.value)
                && same_annotations_in_order(&left.annotations, &right.annotations)
        })
}

#[test]
fn annotated_graphs_in_forward_order_read_back_exactly() {
    // RdfReadAnnotated.map_graph_complete_annotated: the forward mapping of
    // tests/data/dosing-annotated.ofn, the dosing example with two ontology
    // annotations and annotations on 18 axioms, in order, reads back to the
    // same ontology, annotations in order included, with its blank nodes in
    // allocation order. The theorem covers the twelve annotated axioms with one
    // main triple, each reified by a node typed owl:Axiom; the six annotated
    // axioms that a blank node represents are read as well.
    let expected = functional_ontology(DOSING_ANNOTATED_FUNCTIONAL);
    let mapped =
        map_graph(&graph(DOSING_ANNOTATED)).expect("the graph is the image of its ontology");
    let ontology = &mapped.ontology;
    assert!(same_annotations_in_order(
        &ontology.annotations,
        &expected.annotations
    ));
    assert_eq!(ontology.annotations.len(), 2);
    assert_eq!(ontology.axioms.len(), expected.axioms.len());
    for (index, (read, written)) in ontology
        .axioms
        .iter()
        .zip(expected.axioms.iter())
        .enumerate()
    {
        assert!(
            same_body(&read.axiom, &written.axiom),
            "axiom {index} differs"
        );
        assert!(
            same_annotations_in_order(&read.annotations, &written.annotations),
            "annotations of axiom {index} differ"
        );
    }
    let labels: Vec<Vec<u8>> = mapped
        .blanks
        .iter()
        .map(|node| node.label.clone())
        .collect();
    let allocated: Vec<Vec<u8>> = (1..=83).map(|n| format!("b{n}").into_bytes()).collect();
    assert_eq!(labels, allocated);
}

/// Whether two lists of annotations are the same up to their order.
fn same_annotations_up_to_order(left: &[Annotation], right: &[Annotation]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut taken = vec![false; right.len()];
    left.iter().all(|annotation| {
        let found = (0..right.len()).find(|&index| {
            !taken[index]
                && same_annotations_in_order(
                    std::slice::from_ref(annotation),
                    std::slice::from_ref(&right[index]),
                )
        });
        match found {
            Some(index) => {
                taken[index] = true;
                true
            }
            None => false,
        }
    })
}

/// Whether `read` lists the axioms of `written` in some order, each with its
/// annotations in some order.
fn same_annotated_axioms_up_to_order(read: &[AnnotatedAxiom], written: &[AnnotatedAxiom]) -> bool {
    if read.len() != written.len() {
        return false;
    }
    let mut taken = vec![false; written.len()];
    read.iter().all(|axiom| {
        let found = (0..written.len()).find(|&index| {
            !taken[index]
                && same_body(&axiom.axiom, &written[index].axiom)
                && same_annotations_up_to_order(&axiom.annotations, &written[index].annotations)
        });
        match found {
            Some(index) => {
                taken[index] = true;
                true
            }
            None => false,
        }
    })
}

#[test]
fn annotated_graphs_in_any_order_read_back_up_to_order() {
    // RdfReadAnnotatedPermuted.map_graph_complete_annotated_perm: the triples
    // of the forward mapping of tests/data/dosing-annotated.ofn in reverse order
    // and in shuffled orders, with reifications and annotation triples before
    // the axioms they annotate, read back to the same ontology: the same
    // identity, the same imports and ontology annotations up to their order,
    // the same axioms up to their order, each with its annotations up to their
    // order, and the same blank nodes up to their order. The theorem covers the
    // twelve annotated axioms with one main triple; the six annotated axioms
    // that a blank node represents are read as well.
    let expected = functional_ontology(DOSING_ANNOTATED_FUNCTIONAL);
    let mut reversed: Vec<&[u8]> = DOSING_ANNOTATED
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .collect();
    reversed.reverse();
    let mut backwards = reversed.join(&b'\n');
    backwards.push(b'\n');
    let mut sources = vec![backwards];
    for seed in [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233] {
        sources.push(shuffled_lines(DOSING_ANNOTATED, seed));
    }
    let mut allocated: Vec<Vec<u8>> = (1..=83).map(|n| format!("b{n}").into_bytes()).collect();
    allocated.sort();
    for (round, source) in sources.iter().enumerate() {
        assert_ne!(
            &source[..],
            DOSING_ANNOTATED,
            "round {round} reorders the triples"
        );
        let mapped = map_graph(&graph(source))
            .unwrap_or_else(|| panic!("round {round}: the graph is the image of its ontology"));
        let ontology = &mapped.ontology;
        match (&ontology.identity, &expected.identity) {
            (
                OntologyIdentity::Named { ontology, version },
                OntologyIdentity::Named {
                    ontology: expected_ontology,
                    version: Some(expected_version),
                },
            ) => {
                assert!(same_iri(ontology, expected_ontology));
                assert!(matches!(version, Some(version) if same_iri(version, expected_version)));
            }
            _ => panic!("round {round}: both are named with a version IRI"),
        }
        assert_eq!(ontology.imports.len(), 1);
        assert!(same_iri(&ontology.imports[0], &expected.imports[0]));
        assert!(
            same_annotations_up_to_order(&ontology.annotations, &expected.annotations),
            "round {round}: the same ontology annotations"
        );
        assert_eq!(ontology.annotations.len(), 2);
        assert!(
            same_annotated_axioms_up_to_order(&ontology.axioms, &expected.axioms),
            "round {round}: the same axioms and annotations"
        );
        let mut labels: Vec<Vec<u8>> = mapped
            .blanks
            .iter()
            .map(|node| node.label.clone())
            .collect();
        labels.sort();
        assert_eq!(labels, allocated, "round {round}: the same blank nodes");
    }
}
