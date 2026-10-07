# Accepted serialization scope

The user expanded the first-release requirement to standard RDF graph/dataset
formats on 2026-09-30. The public bounded N-Triples and Turtle readers have
**checked byte-to-graph totality and complete-acceptance proofs**, the RDF/XML
reader is **proved exact against the XML 1.0 and RDF 1.1 XML Syntax grammars**
over the verified XML reader (XML literals are declined; see status.md), and
the N-Triples writer and a canonical Turtle writer are **proved by round trips
through them** (Writers, below). The other required formats (N-Quads, TriG,
JSON-LD, RDFa, and the RDF/XML, N-Quads, TriG and JSON-LD writers) are planned.
No complete verified RDF/OWL frontend exists yet.

The shared raw term/dataset representation and explicit graph-selection operation
are now implemented. Lean proves exact graph-name comparison, total selection,
whole-dataset retention, missing-graph acceptance iff and default-selection
acceptance iff names are unique. Raw term lexical validity remains a proof
obligation; the documents of an import closure are read with blank identities
in a scope of their own (`import_catalog`, below). N-Triples reads
exact scoped terms from bytes under a supplied immutable scope and explicit
term/count limits; default limits are input sized. The full verified
multi-format OWL frontend remains pending.

| Format/version | Read | Export | Normative source |
| --- | --- | --- | --- |
| OWL 2 Functional Syntax, second edition | Required | Not added by this change | [OWL structural syntax](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/) |
| RDF/XML, revised syntax | Required | Required | [RDF/XML](https://www.w3.org/TR/2004/REC-rdf-syntax-grammar-20040210/) |
| RDF 1.1 Turtle | Required | Required | [Turtle](https://www.w3.org/TR/2014/REC-turtle-20140225/) |
| RDF 1.1 N-Triples | Required | Required | [N-Triples](https://www.w3.org/TR/2014/REC-n-triples-20140225/) |
| RDF 1.1 N-Quads | Required | Required | [N-Quads](https://www.w3.org/TR/2014/REC-n-quads-20140225/) |
| RDF 1.1 TriG | Required | Required | [TriG](https://www.w3.org/TR/2014/REC-trig-20140225/) |
| JSON-LD 1.1 | Required | Required | [Syntax](https://www.w3.org/TR/2020/REC-json-ld11-20200716/), [processing algorithms](https://www.w3.org/TR/2020/REC-json-ld11-api-20200716/) |
| RDFa 1.1 Core, third edition, with HTML/XHTML host rules | Required | Not required | [Core](https://www.w3.org/TR/2015/REC-rdfa-core-20150317/), [HTML](https://www.w3.org/TR/2015/REC-html-rdfa-20150317/), [XHTML](https://www.w3.org/TR/2015/REC-xhtml-rdfa-20150317/) |

RDF 1.2 additions are a separate draft-version target. N3, TriX, RDF/JSON and
vendor encodings are not silently classified as these finalized Recommendations.
Their addition requires a pinned specification and its own coverage obligations.

## Shared pipeline

Each byte reader feeds one independently specified RDF 1.1 term/graph/dataset
representation. The shared OWL RDF-to-structural mapping then feeds canonical
imports/declarations and DL validation. Functional Syntax enters the structural
stage directly. RDF format correctness and OWL DL admissibility are separate
checks: a valid RDF document can encode a graph that is not a valid OWL 2 DL
ontology. A reader must not invent a DL interpretation for such a graph.

Dataset APIs require **explicit graph selection**, including selection of the
default graph. They retain every unselected graph for inspection and dataset
export. No automatic union or silent named-graph discard is permitted. Blank
node identity shared across graphs in one RDF dataset must be preserved; scopes
across distinct imported documents follow the OWL mapping/include rules.
Graph names, document IRIs and ontology/version IRIs remain distinct identities.

Imports, JSON-LD remote contexts and any other semantic external resources use
the caller-supplied immutable catalog; missing resources are typed errors.
No network fetching or browser script execution enters the verified pipeline.
Parsing an RDFa host document and interpreting JSON-LD contexts are semantic
operations inside the input-byte proof scope, even if an adapter helps with I/O.

Writers prove parse-after-write equality of the represented RDF graph/dataset up
to blank-node isomorphism, preserving named/default graph placement, literal
lexical forms, language tags, datatype IRIs and all unselected graphs. Pretty
printing, prefix choice and blank-node label choice need not preserve bytes.
Single-graph formats require explicit selection from a dataset. If a target
syntax cannot represent a graph (e.g. RDF/XML predicate QName restrictions),
export returns a typed representability error instead of dropping triples.

OWL 2's 2012 RDF mapping predates RDF 1.1 literal conventions. The frontend must
prove the bridge for plain/string/language-tagged literals and blank nodes;
library defaults are not accepted as evidence of semantic agreement. JSON-LD
features beyond standard RDF also need explicit retained metadata or a typed
conversion error; conversion must not silently erase information.

## Implementation and proof order

1. Verified RDF terms/datasets, IRI/base handling, blank-node scope and explicit
   graph selection; prove selection preserves the stored complete dataset.
2. N-Triples reader/writer, with complete grammar and escape/lexical proofs.
3. N-Quads and shared dataset writer laws; then Turtle and TriG grammar expansion.
4. RDF/XML and Functional Syntax full grammars, canonical OWL mapping and imports.
5. JSON-LD context/expansion/to-RDF and writer proofs; RDFa and host parsing proofs.
6. Cross-format semantic equivalence tests, normative conformance suites, format
   error completeness and composition into the byte-to-answer release theorem.

This expands M3 and the M9 release composition; no existing proof is relabeled
as a verified parser or writer. Every listed reader and required writer must
meet its full acceptance/correctness/termination obligations before v0.1.

## Current N-Triples implementation and checks

`rowl::experimental::ntriples` reads a whole UTF-8 source into a raw graph and
exports a graph with an explicit output-byte budget. It preserves term kinds,
exact IRIs, lexical forms, datatype IRIs, language-tag case and repeated raw
triple occurrences. Equal labels in a supplied document scope have one blank
identity. The caller must assign distinct scopes to independent documents; an
import closure gives each document the scope of its catalog position
(`import_catalog::document_scope`). Export labels injectively
encode both raw scope and label keys, including empty/non-UTF-8 opaque keys;
blank labels therefore change on reload, with graph isomorphism as the contract.

The runtime implementation uses the proved absolute-IRI and language-tag
recognizers and scalar encoder. Ill-typed datatype lexical forms remain RDF
literals; later OWL datatype reasoning interprets them. Explicit `rdf:langString`
without a language tag is rejected as an invalid RDF literal kind.

The formal scope proves the encoder and complete language-tag ABNF, including
RFC 5646 well-formedness versus registry validity. It now also proves the actual
unit/required/expected readers, maximal comments and both trivia modes,
fixed-unit output budgets, hex/character predicates, blank-label suffix scans
and exact bounded span copying. The complete blank-node token reader has a
composed byte-to-token proof, acceptance iff the independent grammar holds,
exact caller scope/label preservation and stage-specific diagnostics. Unicode
and short escape payloads now also have totality, complete acceptance, exact
value/scalar validation, IRI-mode restrictions and bounded progress proofs.
The quoted-token caller now composes the actual source backslash, raw units,
opening/closing delimiters, canonical encoding and output budgets. Its totality,
exact first-error relation and complete token acceptance are checked. IRIREF
composes that proof with the RFC 3987 byte recognizer; subject construction
composes exact IRIREF and caller-scoped blank tokens. These proofs cover complete
individual tokens and subject values. Full LANGTAG token recognition now also
composes maximal head/subtag and hyphen scanning, exact original case and bounded
copying with the RFC 5646 recognizer. Acceptance is exact in both directions and
errors preserve their stage offsets. Literal kind binding, full subject/object
construction, triple punctuation/line boundaries and bounded public whole-
document reading now compose those stages with totality and complete-acceptance
proofs. Exact ordered graph occurrences, caller-scope blank identities, repeated
triples, count-limit outcomes and first errors are checked. The RDF-to-OWL
mapping is proved sound, annotated axioms and annotations included, and complete
for every ontology without annotations that it reads back exactly: the graph of
such an ontology, with its version IRI and imports, listed in the order of the
forward mapping, is read back to exactly that ontology, and listed in any order,
to that ontology up to the order of its axioms and imports; with ontology
annotations and annotations on axioms with one main triple, listed in the order
of the forward mapping, it is read back to exactly that ontology, annotations
included, and listed in any order, to that ontology up to the order of its
imports, annotations and axioms and of the annotations of each axiom. The
ontologies are those
that satisfy the reserved-vocabulary and typing conditions of OWL 2 DL, with
axioms, class expressions and data ranges of every kind except equivalences and
equalities of three or more members, inverse-property axioms whose first member
is an inverse and object property assertions on an inverse, which the mapping
writes as triples of other axioms. Canonical identity assignment across imports,
the completeness of the mapping for annotations of annotations and for annotated
axioms that a blank node represents remain pending; the parse-after-write laws
of the writers are proved (Writers, below). Extraction succeeds without unknown external
declarations; Lean checks the registered correctness theorems independently.

```sh
cargo run -p rowl-cli -- check-nt examples/maintenance.nt
cargo run -p rowl-cli -- export-nt examples/maintenance.nt > /tmp/maintenance.nt
python3 scripts/fetch-ntriples-suite.py /tmp/rowl-ntriples-suite
ROWL_NTRIPLES_SUITE_DIR=/tmp/rowl-ntriples-suite \
  cargo test -p rowl-frontend --test ntriples -- --include-ignored
```

All 68 official [W3C N-Triples syntax cases](https://www.w3.org/2013/N-TriplesTests/)
pass. Every positive case is also exported/reloaded and independently checked
for exact terms and a bijection of blank identities. Exact fetched-file hashes
are recorded in `ntriples-suite.json`; the corpus stays outside this repository.
Additional regressions cover every Unicode scalar against Rust's encoder,
malformed input offsets, blank-label punctuation, distinct scope keys, invalid
raw terms, preservation of ill-typed literals and exact byte/count budgets.
The two CLI tests exercise a real maintenance graph and I/O failure handling.
These tests provide evidence and do not replace the outstanding proofs.

## Current Turtle implementation and checks

`rowl_kernel::turtle::read` reads a whole RDF 1.1 Turtle document from its UTF-8
bytes into the same raw graph as the N-Triples reader, against a base IRI and a
blank-node scope that the caller supplies; `read_with_limits` adds limits on the
bytes of a term and the number of triples. It accepts the whole grammar of
section 6.5, with the longest-match tokens of the grammar's note, resolves
relative IRIs by RFC 3986 section 5.2 against the base in force, requires RFC
3987 IRIs and well-formed BCP 47 language tags, and gives the triples in the
order of section 7. Labelled blank nodes keep their labels; the blank node of a
property list or a collection member is labelled `0xFF` or `0xFE` followed by
the decimal byte offset where it begins, which no UTF-8 label can contain. All
blank nodes have the caller's scope, so independent documents need distinct
scopes. A string's lexical form is its characters after unescaping; datatype
IRIs and language-tag case are kept; numbers keep their spelling as lexical
form with the datatype `xsd:integer`, `xsd:decimal` or `xsd:double`.

`Turtle.lean` proves the reader against relations written from sections 6.5 and
7: `read_with_limits_total_correct` (a graph of exactly the denoted triples in
order, or the first error) and `read_with_limits_accepted_iff` (a graph exactly
for Turtle documents within the limits). See m3-m4-progress.md for the parts.

`Reasoner::from_turtle` reads the OWL ontology that a Turtle graph encodes
through the verified reverse RDF mapping, with the scope `document` and no base
of its own (`from_turtle_with_base` supplies one); the CLI's `check`, `classify`
and `instances` commands read `.ttl` files this way, and the Python package
reads Turtle with `syntax="turtle"` or from a `.ttl` file.

```sh
cargo run -p rowl-cli -- classify examples/medication-safety.ttl
```

```sh
python3 scripts/fetch-turtle-suite.py /tmp/rowl-turtle-suite
ROWL_TURTLE_SUITE_DIR=/tmp/rowl-turtle-suite \
  cargo test -p rowl-kernel --test turtle -- --include-ignored
```

All 313 cases of the [W3C RDF 1.1 Turtle suite](https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/)
pass: positive and negative syntax, negative evaluation, and evaluation cases
whose graphs equal the expected N-Triples graphs up to blank-node isomorphism.
Exact fetched-file hashes and the pinned `w3c/rdf-tests` commit are recorded in
`turtle-suite.json`; the corpus stays outside this repository.

## Writers

`rowl_kernel::ntriples::write` and `rowl_kernel::turtle::write` write a raw graph
within an output-byte budget, through one writer (`rdf_write::write_graph`).
Each triple is the line `subject predicate object .`, which is both N-Triples
and Turtle. IRIs are IRIREFs, with UCHARs `\U` and eight hexadecimal digits for
the characters an IRIREF cannot hold raw; strings write `"`, `\`, line feed and
carriage return as ECHARs and every other character raw; every literal carries
its datatype or language tag; a blank node of the scope `s` and the label `l` is
written `_:b` followed by the lowercase hexadecimal digits of the bytes of `s`,
`_` and those of `l`, so distinct blank nodes, of any scopes, get distinct
labels. A graph that a syntax cannot carry gives the first offending term as a
typed error: `InvalidIri` (not an absolute RFC 3987 IRI),
`MalformedLiteralUtf8`, `InvalidLiteralKind` (the datatype rdf:langString) or
`InvalidLanguageTag` (not a well-formed BCP 47 tag of LANGTAG's form), and for
Turtle, whose readers resolve every IRIREF, `IriChangedByResolution` (an IRI
that RFC 3986 section 5.2 resolution changes, such as one with dot segments);
`ResourceLimit` reports an exhausted budget. The Turtle writer is a canonical
subset: no prefixes, abbreviations or pretty printing.

`RdfWrite.lean` gives the text and the faults as Lean functions of the graph
and proves the writers return exactly them (`ntriples_write_total_correct`,
`turtle_write_total_correct`). `RdfWriteRead.lean` proves the round trips: the
verified readers read the written bytes back, in any blank node scope, and for
Turtle against any base IRI shorter than `usize::MAX / 8` bytes, as the
graph's triples in order with every blank node renamed one to one into the
reader's scope (`ntriples_write_read`, `turtle_write_read`,
`written_label_injective`). The N-Triples errors are exact: every N-Triples
document denotes triples without faults, so when the writer reports one, no
N-Triples document denotes the graph up to blank nodes
(`ntriples_write_error_exact`). `IriChangedByResolution` marks the limit of the
Turtle subset only: Turtle can carry some such IRIs through prefixed names.

```sh
cargo run -p rowl-cli -- export-nt examples/maintenance.nt > /tmp/maintenance.nt
cargo test -p rowl-kernel --test writers
```

## Import closures

`import_catalog` and `import_closure` read the import closure of a document
from a catalog of Functional Syntax, N-Triples and Turtle documents that the
caller supplies, as the catalog rules above require: nothing is fetched, and an
import IRI that is the ontology or version IRI of no document of the catalog, or
of several, is a typed error naming the document and the IRI. Every document's
blank nodes or node IDs are anonymous individuals of a scope of its own, so
equal labels in different documents denote different individuals (§5.6.2 of
the Structural Specification). The assembled axiom closure is proved to have
exactly the models of the import closure (see `docs/status.md`). The reverse RDF
mapping reads each RDF document with its own declarations only, not with those
of the documents it imports, as the canonical parsing of the Structural
Specification §3.6 would.
