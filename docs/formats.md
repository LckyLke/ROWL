# Accepted serialization scope

The user expanded the first-release requirement to standard RDF graph/dataset
formats on 2026-09-30. The public bounded N-Triples and Turtle readers now have
**checked byte-to-graph totality and complete-acceptance proofs**. The
N-Triples writer remains experimental, with serialization-isomorphism proofs
pending. The other required formats and Turtle export are planned. No complete
verified RDF/OWL frontend exists yet.

The shared raw term/dataset representation and explicit graph-selection operation
are now implemented. Lean proves exact graph-name comparison, total selection,
whole-dataset retention, missing-graph acceptance iff and default-selection
acceptance iff names are unique. Raw term lexical validity and assigning blank
identities across imported documents remain proof obligations. N-Triples reads
exact scoped terms from bytes under a supplied immutable scope and explicit
term/count limits; default limits are input sized. Its export laws and the full
verified multi-format OWL frontend remain pending.

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
identity. The caller must assign distinct scopes to independent documents;
canonical import scope assignment remains pending. Export labels injectively
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
triples, count-limit outcomes and first errors are checked. Canonical identity
assignment across imports, the completeness of the RDF-to-OWL mapping (proved
sound for axioms without annotations of their own) and parse-after-write graph-
isomorphism laws remain pending. Extraction succeeds without unknown external
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
