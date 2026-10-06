use rowl_kernel::data_ontology::{
    prepare, prepared_consistent, prepared_instance_of, prepared_subsumed,
};
use rowl_kernel::model::*;
use rowl_kernel::ntriples::{read, ReadResult};
use rowl_kernel::probes::Natural;
use rowl_kernel::rdf::RawGraph;
use rowl_kernel::rdf_mapping::map_graph;

const MEDICATION: &[u8] = include_bytes!("../../../examples/medication-safety.nt");
const ANNOTATED_MEDICATION: &[u8] =
    include_bytes!("../../../examples/medication-safety-annotated.nt");
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
