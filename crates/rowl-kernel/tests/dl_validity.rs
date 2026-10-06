use rowl_kernel::data_ontology::{prepare, prepared_consistent, prepared_subsumed};
use rowl_kernel::dl_validity::{
    check_declarations, check_ontology, check_typing, has_anonymous_assertion, has_chain,
    same_bytes, DeclarationCheck, DlCheck, TypingCheck,
};
use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{read_document, DocumentLimits};
use rowl_kernel::functional_model::document_ontology;
use rowl_kernel::indexing::{check_ontology_typing, IndexedTyping};
use rowl_kernel::model::{Axiom, Class, ClassExpression, Iri, RawOntology};
use rowl_kernel::typing::{EntityKind, TypingResult};

fn limits() -> DocumentLimits {
    DocumentLimits {
        tokens: 5000,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 200,
        axioms: 200,
        annotations: AnnotationLimits {
            depth: 3,
            count: 10,
            iri: 200,
            lexical: 200,
        },
        classes: ClassLimits {
            depth: 10,
            count: 10,
            iri: 200,
        },
    }
}

/// The raw ontology of a Functional Syntax document with prefix `:`.
fn ontology(body: &str) -> RawOntology {
    ontology_with("<https://example.org/o>", body)
}

fn ontology_with(header: &str, body: &str) -> RawOntology {
    let source = format!("Prefix(:=<https://example.org/>)\nOntology({header}\n{body}\n)\n");
    let document = read_document(&source.into_bytes(), &limits())
        .unwrap_or_else(|_| panic!("the fixture document reads"));
    document_ontology(&document, &b"test".to_vec()).expect("every read document maps")
}

fn text(iri: &Iri) -> String {
    String::from_utf8_lossy(&iri.spelling).into_owned()
}

fn local(iri: &Iri) -> String {
    text(iri)
        .trim_start_matches("https://example.org/")
        .to_string()
}

/// The verdict's restriction name and its IRI evidence, when it has one.
fn verdict(ontology: &RawOntology) -> (&'static str, String) {
    match check_ontology(ontology) {
        DlCheck::Valid => ("Valid", String::new()),
        DlCheck::EmptyKey(_) => ("EmptyKey", String::new()),
        DlCheck::Arity(_) => ("Arity", String::new()),
        DlCheck::ReservedOntologyIri(iri) => ("ReservedOntologyIri", text(iri)),
        DlCheck::ReservedVersionIri(iri) => ("ReservedVersionIri", text(iri)),
        DlCheck::ReservedEntity { iri, .. } => ("ReservedEntity", text(iri)),
        DlCheck::ConflictingDeclarations { iri, .. } => ("ConflictingDeclarations", local(iri)),
        DlCheck::MissingDeclaration { iri, .. } => ("MissingDeclaration", local(iri)),
        DlCheck::TopDataProperty(_) => ("TopDataProperty", String::new()),
        DlCheck::MissingDatatypeDefinition(iri) => ("MissingDatatypeDefinition", local(iri)),
        DlCheck::PredefinedDatatypeRedefined(_) => ("PredefinedDatatypeRedefined", String::new()),
        DlCheck::MultipleDatatypeDefinitions { .. } => {
            ("MultipleDatatypeDefinitions", String::new())
        }
        DlCheck::DatatypeCycle { .. } => ("DatatypeCycle", String::new()),
        DlCheck::DefinedDatatypeInOntologyAnnotation(_) => {
            ("DefinedDatatypeInOntologyAnnotation", String::new())
        }
        DlCheck::DefinedDatatypePosition(_) => ("DefinedDatatypePosition", String::new()),
        DlCheck::NonSimpleRole(role) => ("NonSimpleRole", local(role.iri)),
        DlCheck::IrregularHierarchy { .. } => ("IrregularHierarchy", String::new()),
        DlCheck::AnonymousPosition(_) => ("AnonymousPosition", String::new()),
        DlCheck::AnonymousSelfLoop(_) => ("AnonymousSelfLoop", String::new()),
        DlCheck::AnonymousCycle { .. } => ("AnonymousCycle", String::new()),
        DlCheck::AnonymousMultipleAssertions { .. } => {
            ("AnonymousMultipleAssertions", String::new())
        }
        DlCheck::AnonymousNoBoundaryRoot(_) => ("AnonymousNoBoundaryRoot", String::new()),
    }
}

fn restriction(body: &str) -> &'static str {
    verdict(&ontology(body)).0
}

const DECLARED: &str =
    "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(ObjectProperty(:r)) \
     Declaration(ObjectProperty(:s)) Declaration(DataProperty(:p))";

#[test]
fn every_restriction_has_a_crafted_violation() {
    let cases = [
        ("HasKey(:A () ())", "EmptyKey"),
        ("DisjointClasses(:A :A)", "Arity"),
        ("SubClassOf(ObjectIntersectionOf(:A :A) :B)", "Arity"),
        (
            "Declaration(Class(<http://www.w3.org/2002/07/owl#Unknown>))",
            "ReservedEntity",
        ),
        ("Declaration(Datatype(:A))", "ConflictingDeclarations"),
        ("SubClassOf(:A :C)", "MissingDeclaration"),
        (
            "DataPropertyAssertion(owl:topDataProperty :i \"1\"^^xsd:integer)",
            "TopDataProperty",
        ),
        (
            "Declaration(Datatype(:D)) DataPropertyRange(:p :D)",
            "MissingDatatypeDefinition",
        ),
        (
            "DatatypeDefinition(xsd:integer xsd:string)",
            "PredefinedDatatypeRedefined",
        ),
        (
            "Declaration(Datatype(:D)) DatatypeDefinition(:D xsd:integer) \
             DatatypeDefinition(:D xsd:string)",
            "MultipleDatatypeDefinitions",
        ),
        (
            "Declaration(Datatype(:D)) Declaration(Datatype(:E)) DatatypeDefinition(:D :E) \
             DatatypeDefinition(:E :D)",
            "DatatypeCycle",
        ),
        (
            "Declaration(Datatype(:D)) DatatypeDefinition(:D xsd:integer) \
             DataPropertyAssertion(:p :i \"1\"^^:D)",
            "DefinedDatatypePosition",
        ),
        (
            "TransitiveObjectProperty(:r) FunctionalObjectProperty(:r)",
            "NonSimpleRole",
        ),
        (
            "Declaration(ObjectProperty(:t)) Declaration(ObjectProperty(:u)) \
             SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t) \
             SubObjectPropertyOf(ObjectPropertyChain(:u :t) :s)",
            "IrregularHierarchy",
        ),
        ("SameIndividual(_:a :i)", "AnonymousPosition"),
        ("ObjectPropertyAssertion(:r _:a _:a)", "AnonymousSelfLoop"),
        (
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:b _:c) \
             ObjectPropertyAssertion(:r _:c _:a)",
            "AnonymousCycle",
        ),
        (
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:s _:a _:b)",
            "AnonymousMultipleAssertions",
        ),
        (
            "ObjectPropertyAssertion(:r :i _:a) ObjectPropertyAssertion(:r :j _:a)",
            "AnonymousNoBoundaryRoot",
        ),
    ];
    for (axioms, expected) in cases {
        let found = restriction(&format!("{DECLARED} {axioms}"));
        assert_eq!(found, expected, "{axioms}");
    }
}

#[test]
fn header_and_ontology_annotation_restrictions_are_checked() {
    let reserved = ontology_with("<http://www.w3.org/2002/07/owl#o>", DECLARED);
    assert_eq!(verdict(&reserved).0, "ReservedOntologyIri");
    let version = ontology_with(
        "<https://example.org/o> <http://www.w3.org/2000/01/rdf-schema#v1>",
        DECLARED,
    );
    assert_eq!(verdict(&version).0, "ReservedVersionIri");
    let annotation = ontology(&format!(
        "Annotation(rdfs:comment \"1\"^^:D) {DECLARED} Declaration(Datatype(:D)) \
         DatatypeDefinition(:D xsd:integer)"
    ));
    assert_eq!(
        verdict(&annotation).0,
        "DefinedDatatypeInOntologyAnnotation"
    );
}

#[test]
fn valid_ontologies_pass_every_restriction() {
    let valid = format!(
        "{DECLARED} Declaration(Datatype(:D)) Declaration(NamedIndividual(:i)) \
         Declaration(AnnotationProperty(:note)) \
         SubClassOf(:A ObjectSomeValuesFrom(:r :B)) DisjointClasses(:A :B) \
         TransitiveObjectProperty(:s) SubObjectPropertyOf(ObjectPropertyChain(:r :r) :r) \
         FunctionalDataProperty(:p) DatatypeDefinition(:D DatatypeRestriction(xsd:integer xsd:minInclusive \"0\"^^xsd:integer)) \
         DataPropertyRange(:p :D) HasKey(:A (:r) ()) ClassAssertion(:A :i) \
         ObjectPropertyAssertion(:r :i _:x) ObjectPropertyAssertion(:r _:x _:y) \
         AnnotationAssertion(:note :A \"a class\") \
         SubDataPropertyOf(:p owl:topDataProperty)"
    );
    assert_eq!(verdict(&ontology(&valid)), ("Valid", String::new()));
    assert_eq!(verdict(&ontology("")), ("Valid", String::new()));
}

#[test]
fn punning_is_allowed_exactly_as_the_typing_constraints_say() {
    // One IRI as a class, an individual and an object property is allowed.
    let punned =
        "Declaration(Class(:A)) Declaration(NamedIndividual(:A)) Declaration(ObjectProperty(:A)) \
         ClassAssertion(:A :A) ObjectPropertyAssertion(:A :A :A)";
    assert_eq!(restriction(punned), "Valid");
    // A class and a datatype, or two kinds of property, may not share an IRI.
    assert_eq!(
        restriction("Declaration(Class(:A)) Declaration(Datatype(:A))"),
        "ConflictingDeclarations"
    );
    assert_eq!(
        restriction("Declaration(ObjectProperty(:A)) Declaration(AnnotationProperty(:A))"),
        "ConflictingDeclarations"
    );
    // Built-in roles count as declarations, and annotation properties need one.
    assert_eq!(
        restriction("SubClassOf(owl:Thing owl:Thing) AnnotationAssertion(rdfs:label :A \"A\")"),
        "Valid"
    );
    assert_eq!(
        restriction("AnnotationAssertion(:label :A \"A\")"),
        "MissingDeclaration"
    );
}

#[test]
fn the_documented_order_decides_which_violation_is_reported() {
    // A missing declaration and an empty key: the key comes first.
    assert_eq!(
        restriction("HasKey(:A () ()) SubClassOf(:A :B)"),
        "EmptyKey"
    );
    // A conflict is reported before a missing declaration that precedes it.
    let both = ontology("SubClassOf(:C :C) Declaration(Class(:A)) Declaration(Datatype(:A))");
    assert_eq!(verdict(&both), ("ConflictingDeclarations", "A".to_string()));
    // Typing before the global restrictions.
    assert_eq!(
        restriction("TransitiveObjectProperty(:r) FunctionalObjectProperty(:r)"),
        "MissingDeclaration"
    );
    // The first missing use in axiom order.
    let order = ontology("Declaration(Class(:A)) SubClassOf(:A :B) SubClassOf(:C :A)");
    assert_eq!(verdict(&order), ("MissingDeclaration", "B".to_string()));
}

#[test]
fn typing_agrees_with_the_symbol_indexed_checker() {
    let fixtures = [
        String::new(),
        DECLARED.to_string(),
        "Declaration(Class(:A)) Declaration(Datatype(:A))".to_string(),
        "SubClassOf(:A :B)".to_string(),
        "Declaration(Class(:A)) ClassAssertion(:A :i) AnnotationAssertion(rdfs:label :A \"A\")"
            .to_string(),
        "Declaration(DataProperty(:p)) Declaration(AnnotationProperty(:p))".to_string(),
        format!("{DECLARED} DataPropertyAssertion(:p :i \"1\"^^:D)"),
        format!("{DECLARED} Declaration(Datatype(:D)) DataPropertyAssertion(:p :i \"1\"^^:D)"),
    ];
    for body in fixtures {
        let ontology = ontology(&body);
        let raw = matches!(check_typing(&ontology), TypingCheck::Valid);
        match check_ontology_typing(&ontology, 1000) {
            IndexedTyping::Checked { result, .. } => {
                assert_eq!(matches!(result, TypingResult::Valid), raw, "{body}");
            }
            IndexedTyping::CapacityExceeded { .. } => panic!("small fixture"),
        }
    }
}

#[test]
fn missing_declarations_report_the_iri_and_its_kind() {
    let missing = ontology("Declaration(Class(:A)) ObjectPropertyAssertion(:r :i :j)");
    match check_typing(&missing) {
        TypingCheck::MissingDeclaration { iri, kind } => {
            assert_eq!(local(iri), "r");
            assert!(matches!(kind, EntityKind::ObjectProperty));
        }
        _ => panic!("hasPart is undeclared"),
    }
}

#[test]
fn declaration_consistency_also_requires_named_individuals() {
    let undeclared = ontology("Declaration(Class(:A)) ClassAssertion(:A :i)");
    assert_eq!(verdict(&undeclared).0, "Valid");
    match check_declarations(&undeclared) {
        DeclarationCheck::Undeclared { iri, kind } => {
            assert_eq!(local(iri), "i");
            assert!(matches!(kind, EntityKind::NamedIndividual));
        }
        DeclarationCheck::Consistent => panic!("i is not declared"),
    }
    let declared = ontology(
        "Declaration(Class(:A)) Declaration(NamedIndividual(:i)) ClassAssertion(:A :i) \
         ClassAssertion(owl:Thing :i)",
    );
    assert!(matches!(
        check_declarations(&declared),
        DeclarationCheck::Consistent
    ));
}

#[test]
fn shortcut_conditions_and_byte_comparison_are_exact() {
    assert!(has_chain(
        &ontology(&format!(
            "{DECLARED} SubObjectPropertyOf(ObjectPropertyChain(:r :s) :r)"
        ))
        .axioms
    ));
    assert!(!has_chain(
        &ontology(&format!("{DECLARED} SubObjectPropertyOf(:r :s)")).axioms
    ));
    let anonymous = |axioms: &str| has_anonymous_assertion(&ontology(axioms).axioms);
    assert!(anonymous("ObjectPropertyAssertion(:r :i _:a)"));
    assert!(anonymous("ObjectPropertyAssertion(:r _:a :i)"));
    assert!(!anonymous(
        "ObjectPropertyAssertion(:r :i :j) ClassAssertion(:A _:a) \
         AnnotationAssertion(rdfs:comment _:a \"anonymous subject\")"
    ));
    for (left, right) in [
        ("", ""),
        ("a", "a"),
        ("ab", "ab"),
        ("ab", "ba"),
        ("a", "ab"),
    ] {
        assert_eq!(
            same_bytes(&left.as_bytes().to_vec(), &right.as_bytes().to_vec()),
            left == right
        );
    }
}

#[test]
fn annotations_do_not_change_reasoning_answers() {
    // The same axioms with and without annotations and annotation axioms.
    let annotated = ontology(
        "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) \
         Declaration(ObjectProperty(:r)) Declaration(AnnotationProperty(:note)) \
         SubClassOf(Annotation(:note \"told\") :A ObjectSomeValuesFrom(:r :B)) \
         SubClassOf(Annotation(Annotation(:note \"nested\") :note \"told\") \
           ObjectSomeValuesFrom(:r :B) :C) \
         AnnotationAssertion(:note :A \"a class\") SubAnnotationPropertyOf(:note rdfs:comment)",
    );
    let plain = ontology(
        "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) \
         Declaration(ObjectProperty(:r)) Declaration(AnnotationProperty(:note)) \
         SubClassOf(:A ObjectSomeValuesFrom(:r :B)) SubClassOf(ObjectSomeValuesFrom(:r :B) :C)",
    );
    assert!(annotated
        .axioms
        .iter()
        .any(|item| matches!(item.axiom, Axiom::AnnotationAssertion(..))));
    let class = |local: &str| {
        ClassExpression::Class(Class {
            iri: Iri {
                spelling: format!("https://example.org/{local}").into_bytes(),
            },
        })
    };
    let left = prepare(&annotated.axioms).expect("the annotated axioms prepare");
    let right = prepare(&plain.axioms).expect("the plain axioms prepare");
    assert_eq!(prepared_consistent(&left), prepared_consistent(&right));
    for (sub, sup) in [("A", "C"), ("C", "A"), ("B", "C")] {
        assert_eq!(
            prepared_subsumed(&left, &class(sub), &class(sup)),
            prepared_subsumed(&right, &class(sub), &class(sup)),
        );
    }
    assert_eq!(
        prepared_subsumed(&left, &class("A"), &class("C")),
        Some(true)
    );
    assert_eq!(verdict(&annotated), ("Valid", String::new()));
}

#[test]
fn built_in_vocabulary_keeps_its_roles_and_positions() {
    // owl:topObjectProperty and owl:bottomObjectProperty are composite (§11.1).
    assert_eq!(
        restriction("FunctionalObjectProperty(owl:topObjectProperty)"),
        "NonSimpleRole"
    );
    assert_eq!(
        restriction("SubClassOf(owl:Thing ObjectMaxCardinality(1 owl:bottomObjectProperty))"),
        "NonSimpleRole"
    );
    assert_eq!(
        restriction("SubClassOf(owl:Thing ObjectSomeValuesFrom(owl:topObjectProperty owl:Thing))"),
        "Valid"
    );
    // owl:topDataProperty only as the superproperty of SubDataPropertyOf.
    assert_eq!(
        restriction("Declaration(DataProperty(:p)) SubDataPropertyOf(:p owl:topDataProperty)"),
        "Valid"
    );
    assert_eq!(
        restriction("Declaration(DataProperty(:p)) SubDataPropertyOf(owl:topDataProperty :p)"),
        "TopDataProperty"
    );
    // Reserved IRIs keep exactly their built-in roles.
    assert_eq!(
        restriction("Declaration(ObjectProperty(owl:Thing))"),
        "ReservedEntity"
    );
    assert_eq!(
        restriction("ClassAssertion(owl:Thing rdfs:label)"),
        "ReservedEntity"
    );
    // No built-in datatype, rdfs:Literal included, may be redefined.
    assert_eq!(
        restriction("DatatypeDefinition(rdfs:Literal xsd:string)"),
        "PredefinedDatatypeRedefined"
    );
}
