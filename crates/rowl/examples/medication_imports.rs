//! The medication-safety example split into two ontologies: a drug vocabulary
//! with the alert rule, in Turtle, and the prescriptions, in Functional Syntax,
//! which import the vocabulary by its version IRI. The import closure is read
//! from a catalog of both documents by the verified readers and assembled by
//! the verified `import_closure`; nothing is fetched. The answers are those of
//! the single-document example, and the OWL 2 DL check sees the imported
//! declarations. An illustration of allergy checking, not clinical guidance.
use rowl::reasoner::{default_limits, named, Document, Reasoner, Syntax};

const MED: &str = "https://example.org/medication/";

fn main() {
    let prescriptions = include_bytes!("../../../examples/imports/medication-prescriptions.ofn");
    let vocabulary = include_bytes!("../../../examples/imports/medication-vocabulary.ttl");
    let catalog = vec![
        Document {
            name: "medication-prescriptions.ofn".into(),
            syntax: Syntax::Functional,
            bytes: prescriptions.to_vec(),
        },
        Document {
            name: "medication-vocabulary.ttl".into(),
            syntax: Syntax::Turtle(Vec::new()),
            bytes: vocabulary.to_vec(),
        },
    ];
    let reasoner = match Reasoner::from_documents(catalog, 0, &default_limits()) {
        Ok(reasoner) => reasoner,
        Err(_) => {
            eprintln!("the import closure could not be read");
            std::process::exit(1);
        }
    };
    println!("import closure: {}", reasoner.documents().join(", "));
    let alert = named(&format!("{MED}AllergyAlert"));
    for person in ["alice", "bob", "carol"] {
        let answer = reasoner.instance_of(&format!("{MED}{person}"), &alert);
        println!("{person} needs an allergy alert: {answer:?}");
    }
    match reasoner.dl_violation() {
        None => println!("OWL 2 DL: valid, with the imported declarations"),
        Some(violation) => println!("OWL 2 DL: not valid: {violation}"),
    }
}
