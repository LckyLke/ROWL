use rowl::experimental::ntriples;
use rowl::experimental::{decide, Atom, Decision, Formula};
use rowl::reasoner::{default_limits, named, LoadError, Reasoner};

fn answer(value: Option<bool>) -> &'static str {
    match value {
        Some(true) => "yes",
        Some(false) => "no",
        None => "unknown (outside the supported fragment)",
    }
}

fn load(path: &str) -> Result<Reasoner, String> {
    let source = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    match Reasoner::from_functional(&source, &default_limits()) {
        Ok(reasoner) => Ok(reasoner),
        Err(LoadError::Document(_)) => Err(format!(
            "{path}: not a Functional Syntax document the verified reader accepts"
        )),
        Err(LoadError::Unsupported) => Err(format!(
            "{path}: the axioms are outside the reasoner's supported fragment"
        )),
    }
}

fn reasoning_command(command: &str, path: &str, extra: &[String]) -> Result<(), String> {
    let reasoner = load(path)?;
    match (command, extra) {
        ("check", []) => {
            println!("consistent: {}", answer(reasoner.consistent()));
        }
        ("classify", []) => {
            if reasoner.consistent() != Some(true) {
                println!("consistent: {}", answer(reasoner.consistent()));
                return Ok(());
            }
            match reasoner.classify() {
                Some(classes) => {
                    for class in classes {
                        if class.satisfiable {
                            println!("{} ⊑ {}", class.class, class.superclasses.join(", "));
                        } else {
                            println!("{} is unsatisfiable", class.class);
                        }
                    }
                }
                None => println!("classification: unknown (outside the supported fragment)"),
            }
        }
        ("instances", [class]) => {
            let expression = named(class);
            for individual in reasoner.individuals() {
                if reasoner.instance_of(&individual, &expression) == Some(true) {
                    println!("{individual}");
                }
            }
        }
        _ => return Err("unknown command".into()),
    }
    eprintln!("Answers come from the verified reader and queries, proved against the OWL 2 Direct Semantics.");
    Ok(())
}

fn nt_command(path: &str, export: bool) -> Result<(), String> {
    let source = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let scope = path.as_bytes().to_vec();
    let graph = match ntriples::read(&source, &scope) {
        ntriples::ReadResult::Graph(g) => g,
        ntriples::ReadResult::Error(e) => {
            return Err(format!(
                "{path}: N-Triples parse error at byte {}",
                e.offset
            ));
        }
    };
    if export {
        let output = match ntriples::write(&graph, usize::MAX) {
            ntriples::WriteResult::Bytes(bytes) => bytes,
            ntriples::WriteResult::Error(_) => return Err("N-Triples export failed".into()),
        };
        use std::io::Write;
        std::io::stdout()
            .lock()
            .write_all(&output)
            .map_err(|e| e.to_string())?;
    } else {
        println!(
            "Parsed {} triple occurrences (N-Triples).",
            graph.triples.len()
        );
    }
    eprintln!("The bounded reader is source-linked and proved; export proofs, canonical import scopes and OWL mapping remain pending.");
    Ok(())
}

fn main() -> std::process::ExitCode {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    match arguments.as_slice() {
        [command] if command == "status" => {
            println!("ROWL development version: M1/M2; M3 indexed closure, UTF-8/XML text checks and exact byte-key symbols; M4 integrated raw-ontology declaration checking with implicit built-ins and ordered axiom preparation.");
            println!("Also: raw RDF datasets with explicit lossless graph selection, and raw-ontology reserved-vocabulary/header checks.");
            println!("Complete RFC 3987 IRI and IRI-reference lexical validation from bytes is also proved; base resolution remains pending.");
            println!("Public bounded N-Triples reading now has composed byte-to-graph totality and complete-acceptance proofs, exact term values, ordered occurrences and first diagnostics.");
            println!("The top-data-property occurrence restriction is checked over the supplied complete axiom closure, with exact first-violation and acceptance proofs.");
            println!("N-Triples reading and experimental export are available; writer laws, canonical import scopes and OWL mapping remain pending.");
            println!("Complete raw role-fact collection is proved: oriented nodes, hierarchy edges, composite seeds, nested simple-role requirements and ordered chains. Non-simple classification and the whole-closure simple-role restriction checker are proved total and complete; full property-hierarchy regularity is also proved, returning a concrete permitted order or an unavoidable conflict.");
            println!("Anonymous positional checking includes recursive annotations on prohibited axiom types. The raw-closure forest checker is proved exact, with scoped byte identities, self-loop and undirected-cycle diagnostics. Distinct annotated-assertion multiplicity and the component-wide named-boundary rule are proved exact, using recursive unordered annotation equivalence. The composed check_anonymous library operation decides all anonymous-individual restrictions and preserves diagnostic priority; byte-derived scopes and other DL validity remain pending.");
            println!("All six raw data-range constructors have total exact structural comparisons with recursive unordered associations. Datatype definitions have proved availability/uniqueness and exact dependency-order checking. The full custom-datatype positional traversal is proved, including literal and restriction-base positions, nested classes/ranges, all axiom forms and recursive annotations. check_structural_datatypes composes definition rules and positions with exact acceptance, original failures and checked priority. Supplied ontology annotations are included; imported ontology annotations require the same complete definition closure. Concrete lexical/facet/value validation remains pending.");
            println!("All 18 class-expression forms have proved exact structural comparisons, recursively unordered members and the owl:Thing/rdfs:Literal cardinality defaults. Reflexivity, symmetry and transitivity are checked. The whole-closure nonempty-key-property checker is also proved total and exact, retaining the original first invalid HasKey; key inference and canonical output remain pending.");
            println!("Structural arity checking now covers the full raw standard class/data/axiom language, counting equivalence classes and recursively checking fillers and nonempty keys. It enforces the documented duplicate-disjointness compatibility rule on original occurrences, preserves repeated ordered chains and returns the first original annotated failure. Canonical output, RDF self-disjointness conversion, lexical/value validity and complete DL validation remain separate.");
            println!("All 37 axiom forms have total exact structural comparison with nested metadata. Unordered sets ignore equivalent repetitions; property chains and distinct inverse-property fields retain order. The full relation is reflexive, symmetric and transitive and agrees with existing assertion/datatype-definition restrictions. Canonical output and model-preserving canonicalization remain pending.");
            println!("Structural comparison now has checked semantic congruence across all data/class/axiom forms. Original arity acceptance and normative interpretation defaults are explicit premises. Structurally matching arity-valid supplied closures preserve models, consistency and source/target entailment under a fixed datatype map and vocabulary; this adds no canonical-output or reasoning algorithm.");
            println!("The actual outer axiom-set builder is proved total: original arities are checked before grouping, stable first representatives and every caller document/ordinal record survive, and all lookups are exact. Selected closures preserve models, consistency and entailment under fixed datatype maps/vocabulary. Nested canonical output, byte-derived provenance and full DL validation remain pending.");
            println!("Functional Syntax prefix/local/abbreviated/node-name byte grammars are proved exact. The immutable prefix table rejects reserved/duplicate names, checks every namespace, preserves original bytes and expands names verbatim with checked byte limits and final absolute-IRI validation. All public operations are proved total; leading source prefix declarations and the ontology opening are proved separately below. Relative resolution and full Functional Syntax parsing remain pending.");
            println!("Complete 2012 Functional Syntax terminal grammars and selection cover all 84 classes: 71 keywords, four punctuation, seven variable and two special terminals. Actual compilation, exact recognition, greatest competing endpoint, token availability and source progress are proved. Complete terminal-language disjointness is also proved, including all 71 distinct keyword spellings. Greatest matching uniquely determines exact token identity and equals actual selection without inventory-priority premises. Other payload kinds and full document parsing remain pending. Quoted-string payload reading now has totality/exact decoding, original diagnostic and output-budget proofs, with both-direction source-grammar equivalence.");
            println!("Generic longest-prefix byte matching is proved total and exact: greatest accepted UTF-8 endpoint, distinct empty/no-match results, bounded source positions and first malformed-suffix errors. Complete Functional Syntax terminal selection and whole-source separator/comment rules are proved in composed stages.");
            println!("Whole-source Functional Syntax tokenization now has composed UTF-8/XML checking, exact regular-token spans, all seven delimiters, greedy trivia removal, emitted-token budgets and first-source diagnostics. Totality and complete acceptance in both directions are proved; later failures reject the entire stream, and invalid-span fallbacks are unreachable. The normative no-ties claim is proved; the separate step-6 prose interpretation is documented in architecture.md. This produces source tokens; ontology grammar/AST construction and reasoning remain pending.");
            println!("Exact decimal integer payloads now have totality, original-span grammar equivalence, both-direction acceptance, positional-value and first-byte diagnostic proofs. Leading zeroes are accepted without a mathematical machine-integer cap. Actual selected integers and every integer in an accepted whole-source token stream have their exact source values. This constructs number payloads; full cardinality-expression/document parsing remains pending. Unary arithmetic, physical resources and cancellation retain their research/M8 limitations.");
            println!("Nonquoted name values now have complete source-linked totality, exact spelling/value grammars, both-direction acceptance and all phase/offset rejection proofs. Full IRI/node/language markers are removed, prefix and abbreviated spellings retained, and budgets count payload bytes. Arbitrary canonical Unicode source segments equal their copied byte interpretation. Actual selected names and all five families in accepted streams supply exact fitting values. The name reader retains abbreviations; source-derived splitting/IRI resolution is proved separately below. Leading prefix declarations and the ontology opening are proved separately below; remaining header/body parsing, roles/scopes and document AST construction remain pending.");
            println!("Source-derived full/abbreviated IRI resolution now has totality, unique exact grammatical parts, complete value/acceptance and all error-phase/offset equivalence proofs. Actual UTF-8 scanning derives the syntax colon, immutable lookup preserves namespaces/local bytes, final budgets count only returned IRI bytes, and the final absolute IRI is revalidated. Internal InvalidParts fallbacks are unreachable. The resolver receives a checked table; the new source prefix reader derives its rows from original bytes. Remaining ontology header/body parsing is pending.");
            println!("Leading Functional Syntax prefix declarations and the exact Ontology opening now have source-linked totality, exact value/acceptance and all syntax/count/payload error proofs. Complete lexing runs first; source rows, original opening tokens and the remaining stream are preserved. The raw rows must pass the normative reserved/duplicate table check. Source parsing, table checking and IRI resolution have composed correctness and exact value/error proofs. Ontology identity/version and leading import targets are proved in the following stage. Annotations, axioms and complete ontology validation remain pending.");
            println!("Source ontology/version identity and maximal leading imports now have totality and exact value/suffix/first-error proofs. Full/abbreviated IRIs retain original tokens and exact final-budget-checked values; import rows preserve original keyword/IRI spans, order and repetitions. Count limits precede each body, and full body syntax precedes IRI resolution. Whole-byte prefix/table/header composition uses exactly source-derived namespaces. Annotations, axioms, unexpected trailing tokens and final closing syntax remain unparsed; canonical catalog/import assembly and full document validity remain pending.");
            println!("Functional Syntax one-literal reading now has exact source value/error and totality proofs, preserved quote/form tokens and suffixes, and strict one/two/three-token progress. Explicit types retain lexical spelling and resolve their original IRI. Plain/tagged strings obligatorily expand to rdf:PlainLiteral with payload+@+exact language spelling; final budgets include the separator and full datatype IRI. Source prefix/table composition uses the original namespaces; callers still supply literal positions. Concrete datatype validity, annotation/axiom grammar, ontology AST and full reasoning remain pending.");
            println!("Functional Syntax annotations, including recursively nested ones, are now read from the source stream with totality and exact result/error proofs. Caller limits bound nesting depth and each sequence's count; properties and IRI values resolve through the checked prefix table, node IDs keep exact labels and literals use the proved literal reader. Anonymous scopes across an import closure remain pending.");
            println!("Functional Syntax entity declarations are read one axiom at a time for all six entity kinds, with axiom annotations from the proved annotation reader and the entity IRI resolved through the checked prefix table. Totality and exact result/error proofs are complete; declaration typing stays the separate kernel check, and the other axiom forms remain pending.");
            println!("The four annotation axioms are read one axiom at a time with the same totality and exact result/error proofs, reusing the proved annotation, value and IRI readers, so every non-logical axiom now has a proved reader. The other logical axioms remain pending.");
            println!("Class expressions of the reasoner's ALC fragment and the class, domain and range axioms are read one at a time with the same totality and exact result/error proofs; the recursive class reader terminates by token count with explicit nesting and member limits. The other logical axioms remain pending.");
            println!("Class assertions and positive and negative object property assertions are read one axiom at a time with the same totality and exact result/error proofs; individuals are IRIs resolved through the checked prefix table or node IDs with their exact labels.");
            println!("The eleven object property axioms, including SubObjectPropertyOf with property chains, EquivalentObjectProperties and TransitiveObjectProperty, are read the same way and mapped into the raw OWL model; the ontology queries reason with inclusions, equivalences and transitivity of named object properties.");
            println!("Whole documents are read by a verified axiom loop over all 37 axiom keywords, through the closing parenthesis and the end of the source, with the same exact result/error proofs; every class expression, data range and axiom form is read. Every read document maps into the kernel's raw OWL model with exact bytes, scoped node IDs and source order, proved against an independent correspondence.");
            println!("Reasoner track: class expressions in the ALC fragment translate to negation normal form, proved total and meaning-preserving under the independent Direct Semantics in every OWL interpretation. The remaining constructors are pending.");
            println!("A verified ALC tableau decides concept satisfiability without a TBox: proved total, sound (explicit tree models) and complete, so each rejection proves a class empty in every OWL interpretation.");
            println!("With a TBox concept that must hold at every element, a second tableau with subset blocking is proved total, sound (Hintikka-family models) and complete, so each rejection proves a class empty in every OWL interpretation where the TBox expression holds everywhere. It also takes inclusions between named object properties and transitive properties (SH), proved against every model of those role axioms.");
            println!("Consistency, class satisfiability and subsumption are answered for axiom closures whose logical axioms are ALC class, domain and range axioms; each answer is proved equal to the Direct Semantics definition, and each acceptance comes with an actual OWL model. Equality between individuals, data assertions and the other axiom forms are pending.");
            println!("These answers also come straight from Functional Syntax source bytes: one extracted function reads the document, maps it into the raw model and queries the reasoner, and each answer is proved exact for the Direct Semantics of the read axioms.");
            println!("A verified completion for named individuals decides concepts at nodes related by named object properties under the TBox and role axioms: proved total, sound (explicit models with a successor model per existential restriction) and complete in every universe. Consistency, satisfiability, subsumption and instance checking now take class and positive and negative object property assertions, also from source text, with each answer proved against the Direct Semantics.");
            println!("Role axioms are read from ontologies and source text: SubObjectPropertyOf between named properties, EquivalentObjectProperties and TransitiveObjectProperty become a role box closed under composition, proved exact for those axioms, and every query decides under it with its answer proved against the Direct Semantics.");
            println!("The queries now cover SROIQ: inverse roles, number restrictions, nominals of named individuals, self restrictions, reflexive, irreflexive, asymmetric and disjoint properties, role chains and the universal and empty roles, decided by a completion forest whose answers are proved against the Direct Semantics. See docs/status.md.");
            println!("Full OWL 2 DL parsing and reasoning are not implemented.");
        }
        [command] if command == "demo" => {
            // Check whether A ∨ B entails A by searching for a counterexample.
            let formula = Formula::And(
                Box::new(Formula::Or(
                    Box::new(Formula::Atom(Atom::A)),
                    Box::new(Formula::Atom(Atom::B)),
                )),
                Box::new(Formula::Not(Box::new(Formula::Atom(Atom::A)))),
            );
            match decide(&formula) {
                Decision::Satisfiable(witness) => {
                    println!("Internal Boolean demo: A ∪ B does not entail A.");
                    println!("Counterexample element: A={}, B={}", witness.a, witness.b);
                }
                Decision::Unsatisfiable => println!("No counterexample exists."),
            }
        }
        [command, path, extra @ ..]
            if command == "check" || command == "classify" || command == "instances" =>
        {
            if let Err(error) = reasoning_command(command, path, extra) {
                eprintln!("{error}");
                return std::process::ExitCode::FAILURE;
            }
        }
        [command, path] if command == "check-nt" || command == "export-nt" => {
            if let Err(error) = nt_command(path, command == "export-nt") {
                eprintln!("{error}");
                return std::process::ExitCode::FAILURE;
            }
        }
        _ => {
            eprintln!("Usage: rowl <status|demo|check FILE|classify FILE|instances FILE CLASS|check-nt FILE|export-nt FILE>");
            eprintln!("export-nt writes N-Triples to standard output.");
            return std::process::ExitCode::FAILURE;
        }
    }
    std::process::ExitCode::SUCCESS
}
