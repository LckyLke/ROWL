# ROWL

A correctness-first Rust research project targeting **full OWL 2 DL under the
OWL 2 Direct Semantics**, with Lean proofs connected to the implementation by
Charon and Aeneas. Intended license: MIT OR Apache-2.0.

**Current status: M1/M2 complete; verified components of M3/M4 are working.**
The Rust model represents all standard OWL 2 DL constructs; Lean defines their
independent meaning and checks semantic laws. The executable reasoner currently
decides Boolean expressions over exactly two atomic classes. New verified stages
resolve a supplied document-import graph, collect explicit entities across the
full raw OWL AST, intern exact byte IRIs into stable symbols, inject implicit
built-in declaration roles and check declarations directly from a raw ontology,
decode strict UTF-8/XML-character text, validate complete RFC 3987 IRIs and
IRI references from bytes, select one explicit graph while retaining
the complete raw RDF dataset, check reserved entity/header vocabulary,
check forbidden anonymous individuals throughout nested expressions/axioms,
collect complete raw role-preprocessing facts with exact inverse orientations,
hierarchy edges, composite seeds, nested simplicity requirements and ordered chains,
classify non-simple properties through cyclic hierarchies and check the entire
simple-role restriction with an exact first-violation diagnostic,
decide the complete property-hierarchy regularity condition with a concrete
permitted ordering or an unavoidable hierarchy conflict,
canonicalize inverse assertions and
prepare ordered annotated axiom batches with model equivalence. UTF-8 encoding
and full language-tag grammar are also proved. N-Triples trivia and complete
blank-node token parsing now have soundness, completeness and termination
proofs with exact source offsets and identity preservation. Unicode/short escape
payloads also have exact value, acceptance, termination and progress proofs.
The public bounded N-Triples reader now has composed byte-to-graph totality and
complete-acceptance proofs, preserving exact ordered triples and first source
diagnostics. Functional Syntax prefix/local/abbreviated/node name grammars and
immutable prefix-table checking and expansion are also proved. Expansion keeps
exact namespace/local spelling and checks output byte limits and the final IRI.
Complete Functional Syntax terminal grammars and selection across all 84 terminal
classes now have exact acceptance, maximum-endpoint and progress proofs. The
whole-source lexer composes XML validation, separators, trivia removal, token
budgets and first-offset diagnostics with totality and complete-acceptance proofs.
Its emitted source spans are ordered, bounded and grammar-valid. Complete terminal
language disjointness is also proved, so greatest matching uniquely determines
each token without relying on implementation priority. Document assembly remains pending. The
quoted-string payload reader now has composed exact decoding, byte-budget,
first-offset and source-grammar equivalence proofs, preserving multiline text.
The exact decimal reader now supplies nonnegative integer payload values from
original source spans, accepting leading zeroes without a machine-integer cap.
Totality, both-direction source/grammar acceptance, positional values and first
invalid-byte offsets are proved. Actual selected integers and every integer in
a successful whole-source token stream have their exact source values. Unary
arithmetic remains a research representation; full document parsing and physical
resource/cancellation control remain pending.
Nonquoted name values now also have source-linked totality, exact spelling,
value-grammar, complete acceptance and exact phase/offset rejection proofs.
Full IRIs, prefixes, abbreviated names, blank labels and language tags preserve
their original spelling while removing only the specified syntax markers.
Canonical source segments/copies are proved equivalent for arbitrary Unicode;
actual selected names and complete lexer streams supply their exact fitting
values. Source-derived abbreviated-IRI splitting and full/abbreviated IRI
resolution now compose the immutable prefix table, exact namespace/local bytes,
final output budgets and absolute-IRI validation. Exact parts are uniquely
determined; totality, value/acceptance and all error phases in both directions
are proved, and internal splitting fallbacks are unreachable. Leading prefix
declarations and the exact `Ontology(` opening are now read from the original
bytes, with totality, complete value acceptance, exact syntax/count/payload
errors and untouched remaining tokens proved. The checked table preserves
precisely those source declarations; parsing, table checking and source IRI
resolution have composed correctness and exact value/error proofs. This partial
stage does not validate ontology contents. The following ontology/version IRI
and maximal leading-import stage is now also proved: exact source values,
original reference tokens, ordered repeated imports, unchanged suffixes and
every first syntax/resolution/count error. Its type permits a version only with
an ontology IRI. Source prefix/table/header composition uses the declarations
from the same original bytes. Annotations are read by the separate stage below;
axioms, scopes, complete document construction and canonical import assembly
remain pending.
One-literal Functional Syntax reading now also has totality, exact source
value/error equivalence, original quote/form tokens, intact suffixes and exact
one/two/three-terminal progress proofs. Explicit types preserve decoded lexical
spelling and resolve their original datatype IRI. Plain strings obligatorily
expand to rdf:PlainLiteral (`"Pump"` becomes lexical `Pump@`; `"Pump"@de`
becomes `Pump@de`), preserving original language case. Final lexical/type budgets
include the separator and the entire datatype IRI. Source prefix/table composition
uses precisely the original parsed namespaces; literal positions still come from
the caller. Concrete datatype lexical/value/facet validity and complete ontology
axiom/AST parsing remain pending.
Functional Syntax annotations, including recursively nested ones, are now read
as the maximal leading `Annotation` sequence, for example the ontology annotations
after the header. Properties and IRI values resolve through the checked prefix
table, node IDs keep their exact label and literals use the proved literal reader.
Caller limits bound the nesting depth and each sequence's count. Totality, exact
result/error equivalence and an independent success grammar are proved, and the
source composition uses the namespaces parsed from the same bytes. Anonymous
scopes, axioms, the closing token and complete document construction remain pending.
Entity declarations, `Declaration( {Annotation} Class(IRI) )` and the five other
entity kinds, are now read one axiom at a time with the same proof guarantees.
Axiom annotations reuse the annotation reader; the entity IRI resolves through the
checked prefix table. Declaration typing stays the existing kernel check, and the
axiom loop and the other axiom forms remain pending.
The four annotation axioms (`AnnotationAssertion`, `SubAnnotationPropertyOf`,
`AnnotationPropertyDomain`, `AnnotationPropertyRange`) are read the same way, so
every non-logical axiom now has a proved reader. The logical axioms, the axiom
loop and complete document construction remain pending.
The reasoner track has started: class expressions in the ALC fragment translate
to negation normal form, proved to keep their meaning under the independent
Direct Semantics in every OWL interpretation. The tableau that decides these
concepts is the next stage.
All 68 W3C N-Triples syntax cases pass. Export laws, the other required
serializations, canonical OWL imports, DL validation and reasoning remain future work;
version 0.1 is not ready for release.

```sh
python3 scripts/bootstrap.py       # Python 3.12+; pinned Linux x86_64 tools
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cargo test --workspace
cargo run -p rowl-cli -- demo
cargo run -p rowl-cli -- check-nt examples/maintenance.nt # experimental RDF parser
cargo run -p rowl-cli -- export-nt examples/maintenance.nt # RDF bytes on stdout
cargo run -p rowl --example maintenance # constructs a raw OWL ontology
cargo run -p rowl --example symbols     # exact byte identities and capacity outcomes
cargo run -p rowl --example iri         # complete IRI and reference lexical checks
cargo run -p rowl --example prefixes    # exact maintenance vocabulary name expansion
cargo run -p rowl --example functional  # maintenance tokens, quoted text and exact cardinality number payloads
cargo run -p rowl --example functional_iris # original source names become exact absolute IRIs
cargo run -p rowl --example functional_prefixes # read source declarations, check the table and resolve source IRIs
cargo run -p rowl --example functional_header # source ontology/version identity and import targets with original offsets
cargo run -p rowl --example functional_literals # exact text/language/type values from original maintenance source
cargo run -p rowl --example functional_annotations # nested ontology annotations from original maintenance source
cargo run -p rowl --example functional_declarations # entity declarations with axiom annotations from original source
cargo run -p rowl --example functional_annotation_axioms # declarations and annotation axioms of a vocabulary ontology
cargo run -p rowl --example nnf         # negation normal form of maintenance class expressions
python3 scripts/verify.py          # re-extract actual Rust, check proofs/audit
```

The demo finds an element in B but not A, demonstrating why membership in A ∪ B
does not entail membership in A. Search must consider every interpretation.

## Layout

| Path | Responsibility |
| --- | --- |
| `crates/rowl-kernel` | Boolean kernel, raw OWL model, exact byte symbols, built-ins, raw-ontology declaration/vocabulary checks, ordered semantic preparation and ALC negation normal form |
| `crates/rowl-frontend` | Indexed catalog closure, UTF-8/XML text checks, complete IRI/name/Functional terminal grammars, proved whole-source token streams, source prefix/ontology identity/import/literal/annotation/declaration/annotation-axiom stages, quoted payload reading and source IRI resolution, raw RDF terms/datasets, proved graph selection/language tags/UTF-8 encoding; N-Triples reading and experimental export |
| `crates/rowl` | Future immutable snapshot API; currently experimental exports only |
| `crates/rowl-cli` | Thin CLI; `status`, `demo`, experimental `check-nt` and `export-nt` |
| `verification` | Actual generated Rust translation, independent semantics, Lean proofs |
| `docs/coverage.json` | Requirement inventory; planned obligations are not proof claims |
| `docs/architecture.md` | Accepted scope, semantic pitfalls, milestones and release gates |
| `verification/toolchain.json` | Pinned tools, translation boundary and trusted assumptions |
| `docs/status.md` | Completed milestones and precise proof boundary |
| `docs/m2-semantics.md` | Standard-to-formal-specification mapping and semantic examples |
| `docs/m3-m4-progress.md` | Current frontend, declaration/vocabulary and preparation proofs and their precise input contracts |
| `docs/formats.md` | Accepted graph/dataset read/export scope and planned correctness contracts |

The Rust maintenance example represents a pump with a faulty motor and the rule
that machines with faulty parts need inspection. Lean checks that these premises
imply the pump needs inspection. Its actual Rust declaration checker reports an
omitted `FaultyPart` declaration, then accepts after adding it. It derives its
symbol tables from the raw AST and includes implicit built-ins. Automatic
full-OWL inference is a later milestone. The example then demonstrates why a
separate reserved-vocabulary check rejects retyping `owl:Thing` as a property.
It also demonstrates the proved top-data-property occurrence check: faultCode
may be a subproperty of owl:topDataProperty, while declaring that top property
functional is rejected. The simple-role checker then rejects a cardinality
restriction on transitive hasPart and accepts after transitivity is removed.
It also checks a hasPart/hasPart-to-nestedPart chain, then rejects adding
a reverse nestedPart-to-hasPart hierarchy edge.

The symbol example assigns stable numeric identifiers to exact byte spellings,
reuses an identifier when its spelling repeats and preserves the table when its
configured symbol-count budget is full. Raw `Iri.spelling` now uses `Vec<u8>`;
the symbol table operates directly on this representation. Lexical validity and
a verified byte parser remain separate obligations.

The raw dataset API requires an explicit default or named graph choice. A successful
selection borrows the original dataset, retaining every other graph, empty named
graphs, raw literal forms and shared blank-node identities. Missing graphs and
duplicate graph names are separate errors. The reserved-vocabulary check separately
rejects using `owl:Thing` as an object property, even though generic declaration
typing allows class/property punning. These operations do not certify lexical
validity, parser-assigned scopes or complete OWL DL validity.

## Release contract

The first release requires the entire chosen OWL 2 DL language, a complete
normative datatype map, and mechanically checked soundness, completeness and
termination from input bytes through queries. Accepted format coverage also
includes RDF/XML, Turtle, N-Triples, N-Quads, TriG and JSON-LD read/export, and
RDFa read. Datasets require explicit graph
selection while preserving other graphs. N-Triples has source-linked proofs
for its bounded public byte-to-graph reader; its writer remains experimental.
Canonical import scope assignment and OWL RDF mapping remain pending, as do the
other required parsers.
Internal fragment experiments are allowed; a fragment implementation does not
qualify as v0.1.

Definitive answers remain conditional on valid input and sufficient machine
resources. Cancellation and exhaustion must produce typed operational outcomes.
Logical correctness means consequences of the supplied ontology; it cannot
establish that the supplied facts are true in the world. Rust memory safety and
exhaustive enum matches alone do not establish logical correctness.

The supplied raw axiom closure also has a proved anonymous assertion-graph
forest checker. It detects self edges and undirected cycles using exact scoped
byte identity. Repeated endpoint pairs are one graph edge. A separate proved assertion-set
multiplicity checker counts distinct annotated assertions and accepts equivalent
copies, using recursive unordered annotation equivalence. The named-boundary
checker proves complete component-wide search, including isolated vertices.
`experimental::anonymous_restrictions::check_anonymous` composes all anonymous
restrictions with exact acceptance and diagnostic-priority proofs. Its input is
still a caller-supplied complete standardized-apart closure. The positional checker
includes nested annotations on prohibited axiom types. These are experimental
components, not a complete OWL DL validator or reasoner.
