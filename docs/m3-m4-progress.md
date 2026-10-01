# M3 and M4 verified components

These milestones are in progress. Their full exit criteria are unchanged.
The current executable components are exported through `rowl::experimental`.
The verified components are extracted from actual Rust, proved in Lean and
included in the combined axiom audit. N-Triples has an additional experimental
runtime writer whose complete proofs remain pending; its public bounded reader
now has composed byte-to-graph proofs. The proved byte
components cover text, IRIs, UTF-8 encoding and language tags. No complete
verified OWL document parser, DL validator or OWL decision procedure is advertised.

## M3: document closure

`rowl_frontend::imports::resolve` accepts a root document symbol and an owned,
immutable `DocumentCatalog`. Each catalog record supplies a distinct `u32`
lookup symbol, verbatim bytes and explicit dependency symbols. The algorithm
uses a deterministic worklist; it removes a newly discovered document from the
available catalog and records it before visiting its dependencies. Already
resolved symbols are skipped. Output order is reverse discovery order, not
source/catalog order.

The independent specification uses reflexive-transitive graph reachability:
`Rowl.Imports.Reachable`. `resolve_total_correct` proves termination and:

- `Complete`: exactly the reachable keys, no duplicate keys and every returned
  document record (including bytes and dependencies) belongs to the input catalog.
- `MissingDocument`: a reachable key absent from the input catalog, including
  an absent root. Unreachable missing dependencies do not affect this root.
- `DuplicateDocument`: a key occurring at least twice in the catalog. The whole
  supplied catalog is checked for ambiguity before traversal, even unreachable
  entries; repeated *import edges* are harmless.

`resolve_complete_iff` proves success is possible exactly when catalog keys are
unique and all reachable keys are present. `resolve_terminates` excludes
divergence in the translation model without a fuel assumption. The proof uses
a partition/frontier invariant and a lexicographic decreasing measure: remaining
catalog length, then worklist length. It covers cycles and shared dependencies,
not merely acyclic examples.

The catalog is consumed by the Rust operation; it is never modified through
shared access or fetched from a network. This is a symbol-indexed topology stage,
not yet the accepted document-IRI/byte frontend. Parsing document IRIs/imports
from bytes, ontology/version identity constraints, declarations per document's
own import closure, RDF headerless includes, anonymous standardization apart
and axiom provenance remain pending. In particular, callers cannot justify
supplied metadata merely by asserting it matches the document bytes.

The normative reason for the stage ordering is canonical parsing CP2–CP3:
discover documents/import declarations before using imported declarations to
disambiguate syntax. Declarations can follow uses and imports can be cyclic.
See [Structural Specification §3.6](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Canonical_Parsing_of_OWL_2_Ontologies).
RDF headerless documents also require the distinct include transformation in
[RDF Mapping §3.1.1](https://www.w3.org/TR/2012/REC-owl2-mapping-to-rdf-20121211/#Resolving_Included_RDF_Graphs).

## M3: strict UTF-8 and XML-character text

`rowl_frontend::unicode::decode_next` reads exactly one RFC 3629 unit at a
supplied byte offset. The independent `Prefix` specification uses natural-number
byte grammar and values, separate from the Rust machine arithmetic. The proof
covers all offsets and proves every arithmetic/index operation is safe in the
translation model. It distinguishes end-of-input, an invalid position, and an
invalid UTF-8 unit. Returned scalars advance by the exact width, stay within the
input, exclude surrogates, and cannot exceed U+10FFFF. Overlong encodings are
rejected. Diagnostics point to the unit's first byte, not necessarily the first
incorrect continuation byte.

`xml_character` is proved equivalent to XML 1.0 `Char`. `read_text` consumes the
entire UTF-8 vector, returning each code point with its original byte offset or
the first invalid unit/forbidden character. `read_text_total_correct`,
`read_text_valid_iff` and `read_text_terminates` establish totality, exact
acceptance and termination; the independent `TextFrom` and `Rejected` relations
also prove accepted/rejected outcomes cannot both describe the input. Tests
compare every Unicode scalar with Rust's encoder and cover malformed units,
XML boundaries, multibyte offsets and CR/LF preservation.

This component does not tokenize OWL, parse XML, normalize line endings, strip a
BOM or detect encodings. A BOM is preserved as U+FEFF. Valid UTF-16 XML requires a
later decoding stage; a failed UTF-8 check does not establish that arbitrary
RDF/XML input is invalid. XML-discouraged but permitted characters remain
accepted, matching `Char` rather than a stricter application policy.

`rowl_frontend::snapshot::resolve_texts` composes the already proved indexed
closure with text validation. Missing/duplicate catalog errors take precedence;
only reachable records are checked, in resolver output order. Successful output
is the same closure with verbatim bytes/dependencies. A text failure identifies
the first failing document and unit offset in that order. Acceptance is exactly
all reachable records satisfying the text specification, given a complete
closure. Four new Snapshot theorems establish both component correctness and
composition; explicit import metadata remains an input contract.

References: [RFC 3629 §4](https://www.rfc-editor.org/rfc/rfc3629#section-4),
[XML 1.0 §2.2](https://www.w3.org/TR/2004/REC-xml-20040204/#charsets), and
[OWL Functional Syntax §2.2](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Functional-Style_Syntax).
The expanded standard serialization scope is tracked in [formats.md](formats.md)
and the release ledger; N-Triples reading now has bounded byte-to-graph proofs,
while its experimental writer's serialization proofs remain pending.

## M3: exact byte-key symbols

`rowl_kernel::symbols` supplies `empty`, `same_spelling`, `lookup`, `key_of`
and `intern`. A table borrows original byte vectors and has a caller-selected
`u32` symbol-count limit. Its fields are private; callers create a table with
`empty` and obtain later tables from `intern`. Equality compares every byte and
the sequence length. It performs no hashing or lexical normalization.

`InternResult::Existing` reuses the first symbol and its original stored key.
`Inserted` appends the key with the previous table length as its zero-based
symbol. `CapacityExceeded` leaves the complete table unchanged. Duplicate lookup
still succeeds when the table is full; a zero limit is valid.

The independent specifications use lists of byte lists and first matching list
indices. `WellFormed` requires distinct byte keys and a count within the limit.
Seven public proofs establish exact equality, an initially valid empty table,
forward and reverse lookup, all three insertion outcomes, invariant preservation,
preservation of every old symbol and distinctness of valid symbols' keys. The
total-correctness proofs establish safe index arithmetic and terminating
execution in the translation model. The insertion theorem requires the table
invariant, and `empty`/`intern` preserve it for the public Rust construction API.

For example, `cargo run -p rowl --example symbols` interns `FaultyPart` as 0,
`Machine` as 1 and reuses 0 for a repeated `FaultyPart`. With a two-symbol budget,
`NeedsInspection` returns `CapacityExceeded`, and symbol 0 still retrieves the
original `FaultyPart` bytes. Tests also compare insertion histories against an
independent ordered-map oracle and retain percent spelling, case, Unicode,
empty, NUL and non-UTF-8 variants exactly.

This is a byte-key primitive for a future verified lexical pipeline. It does
not itself invoke UTF-8 or IRI validation, expand prefixes or resolve relative references.
The raw AST's `Iri.spelling` now uses exactly this byte-buffer representation;
the composed checker below interns it directly. OWL's exact IRI spelling identity is described in
[Structural Specification §2.4](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#IRIs);
the byte-to-valid-IRI correspondence remains a separate proof obligation. The
pinned extraction supplies no supported model for Rust `String` equality or
`str::as_bytes`, which is why IRI spelling storage changed. No unproved external
axiom was accepted to bridge that gap. Count-capacity handling does not establish a physical memory/stack
exhaustion contract.

## M3: raw RDF datasets and explicit graph selection

`rowl_frontend::rdf` now supplies raw RDF 1.1 term positions: IRI/blank subjects,
IRI predicates and IRI/blank/literal objects. Literals keep lexical bytes and
either a datatype IRI or language tag; language-tagged terms have the implicit
`rdf:langString` datatype. Blank nodes carry opaque scope/label identity keys,
which may be shared across graphs. Graphs store triple vectors, interpreted by
`Rowl.Rdf.GraphContains` as set membership while retaining raw order/repetitions.
A dataset stores one default graph and zero or more named records, including
empty named graphs. Raw records can have duplicate graph names.

`select_graph` requires an explicit `GraphChoice::Default` or `Named` choice.
It rejects duplicate names anywhere in the raw dataset before selection, returns
`MissingGraph` for an absent requested name and returns a `DatasetSelection`
for an existing unique graph. Successful selections expose `selected_graph` and
`original_dataset`; the latter retains the entire immutable input. No graph
union, renaming, scope reassignment, literal normalization or triple dropping is
performed. Raw name equality uses exact bytes and distinguishes IRI names from
scoped blank names.

Five public proofs establish exact graph-name equality, total selection with
genuine duplicate/absence diagnostics, whole-dataset retention, missing iff the
requested graph is absent in a unique-name dataset, and default success iff names
are unique. Regressions cover the selected maintenance graph and retained audit
graph, duplicate raw triples, shared motor blank identity, `01` literal spelling,
language tags, empty versus missing graphs, exact Unicode/case/percent names,
and invalid duplicate names in unselected records.

These are **raw structures and a proved selection operation**. They do not check
UTF-8, absolute IRI grammar, language-tag validity, RDF term well-formedness or
parser-assigned blank scopes. Dataset-preservation proofs retain supplied scope
keys; they do not prove that a parser assigned the keys correctly. The dataset-selection block does not finish serialization mapping/round-trip
laws or the OWL 2012/RDF 1.1 literal bridge. A later experimental N-Triples
reader/writer is described below; bounded reading is now proved, while writer
laws remain pending. The normative
structural reference is [RDF 1.1 Concepts §3–4](https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/).

## M4: declaration typing

`rowl_kernel::typing::validate_typing` accepts supplied symbol/role tables of
declarations and occurrences. Its independent `WellTyped` predicate precisely
captures these declaration constraints:

- Class and Datatype declarations cannot share a symbol.
- ObjectProperty, DataProperty and AnnotationProperty declarations are pairwise
  incompatible on one symbol.
- Every class, datatype and property use requires a matching declaration.
- Named-individual declarations are optional. Other role combinations, including
  class/individual and class/property reuse, are allowed. Repeated declarations
  of the same kind are harmless.

`entity_kind_total_correct` connects all six raw entity variants to the role
table. `validate_typing_total_correct` proves termination with either a valid
table or a genuine conflicting/undeclared symbol. `validate_typing_valid_iff`
proves acceptance iff `WellTyped`; it does not just prove that returned errors
are plausible. Conflict diagnostics take precedence over missing declarations.

The normative reference is [§5.8.1](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Typing_Constraints_of_OWL_2_DL).
Tables must include all relevant occurrences and implicit built-in declarations.
Collection, exact raw IRI interning, implicit built-ins and the original-spelling
declaration acceptance theorem are now composed below. Canonical per-document
composition with parsing and IRI lexical validation remains pending. A successful declaration check is neither a
`ValidatedOntology` nor a logical consistency result. Simple-role restrictions,
hierarchy regularity, datatype definitions, topDataProperty restrictions,
anonymous-individual restrictions and the remaining DL conditions are pending.

## M4: explicit entity and declaration collection

`rowl_kernel::collection` traverses the actual raw OWL AST. Seven experimental
entry points collect from an entity, class expression, data range, annotation,
annotated axiom, whole ontology or its supplied axiom list. The output borrows the original `Iri` values
and carries `EntityKind` roles; spellings are preserved exactly without cloning,
lexical normalization, deduplication or symbol interning. A whole-ontology result
separates declarations from uses. Declaration bodies also count as uses.

The independent Lean specification describes ordered lists of `(Iri, EntityKind)`
with exhaustive matches for all six entity variants, 18 class-expression forms,
six data-range forms and 37 axiom variants. All seven public total-correctness
proofs establish successful termination and exact sequence equality. The vector
proof establishes safe index arithmetic, then recursive syntax-size measures
establish termination for arbitrary finite nested expressions and annotations.
Each proof applies to the actual Aeneas extraction; the inventory gate also
checks the specification's constructor coverage against the Rust model.

The order is structural: children of expression lists remain in order; nested
annotations precede their annotation property/value; axiom annotations precede
the body; ontology annotations precede all axiom occurrences. Repeated IRIs and
roles are retained. Object inverses yield the underlying object-property role.
Literal occurrences contribute their datatype. Only explicit cardinality
fillers contribute roles; absent fillers add no implicit vocabulary.

Annotation subject/value IRIs, annotation-property domain/range target IRIs,
facet IRIs, ontology/version/import IRIs and anonymous labels have no entity
role merely because they are IRIs or identifiers. They are excluded. Annotation
properties and the datatypes of literal annotation/facet values are included.
These distinctions follow the structural positions in the
[OWL specification](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/).

Whole-ontology output includes ontology annotations for structural inspection;
the §5.8.1 typing check is formulated over the relevant axiom closure. Neither
this collector nor `validate_typing` constructs canonical per-document closures.
`axiom_closure_entities` deliberately excludes ontology-level annotations while
retaining every nested axiom annotation. It collects the supplied axiom list;
it does not traverse imports or standardize anonymous individuals apart. The
spelling-to-symbol interner, implicit built-in table and their composition are
now proved below. The collector accepts raw syntax,
including lexically invalid IRI spellings; it does not establish DL validity or
correspondence to serialized bytes. Caller-supplied source/item/ordinal tags
are metadata rather than parser-derived byte provenance.

## M4: composed raw-ontology declaration checking

`rowl_kernel::indexing::index_ontology` invokes the axiom-list collector and
interns declarations before uses. Numeric occurrence lists retain exact order,
roles and repetitions. Its symbol table borrows the original `Vec<u8>` IRI
spellings. A count-capacity failure identifies an actual input IRI, retains a
well-formed partial table and cannot be confused with completed indexing.
`index_entities` exposes the same operation on an owned collected result.

`rowl_kernel::builtins::builtin_kind` recognizes the 49 exact built-in IRIs from
Structural Specification Table 5, §4 and §5.5. `Rowl.Builtins.role` is an
independent finite association-list specification. Total correctness covers
every byte vector, not just those names. The source/axiom gate checks the Rust
branches and formal table against `builtin-vocabulary.json`. Datatype names
have declaration roles here; no datatype lexical/value/facet solver is implied.

`add_builtin_declarations` prepends virtual declarations for every relevant
built-in occurrence, preserving the complete explicit suffix. It recognizes
built-ins independently of the role used in the source. Thus an explicit class
declaration of `xsd:integer` conflicts with its implicit datatype declaration.
Repeated virtual declarations are harmless. Unused built-ins need no numeric
slot: their distinct predefined roles cannot conflict with an unused input IRI.

`check_ontology_typing` composes collection, interning, implicit roles and the
proved declaration validator. `check_ontology_typing_total_correct` establishes
successful terminating execution in the translation model with a declaration
result or typed count-capacity outcome. `check_ontology_typing_valid_iff_raw`
proves that every completed indexing run returns `Valid` exactly when
`RawWellTyped` holds on the original IRI spelling lists with their implicit
built-in declarations. `indexed_identity_iff_spelling` and
`typing_iff_original_spelling` establish the symbol/raw identity bridge and
predicate equivalence. No caller-provided numeric occurrence table is assumed.

The maintenance example actually reports the missing `FaultyPart` declaration,
then passes after adding it. Regressions cover compatible punning, incompatible
retyping, exact Unicode/percent/case spelling, duplicate occurrences, capacity
failure in either input list, and the distinction between ontology-level and
axiom annotations. Ontology annotations remain available in the structural
collector but do not add §5.8.1 axiom-closure declaration requirements.

This is end-to-end **declaration checking of the supplied raw axiom list**.
It does not parse bytes, assemble imports, validate UTF-8/absolute IRI grammar
or reserved-vocabulary usage, check literal/facet validity, enforce the global
DL restrictions, build role automata or finish normalization. In particular,
an ontology's `imports` field is not resolved by this operation; its caller must
already have assembled the intended axiom list. No `ValidatedOntology` or full
M3/M4 completion claim follows from a `Valid` declaration result.

## M4: reserved vocabulary and headers

`rowl_kernel::vocabulary::check_reserved_vocabulary` operates on the actual raw
ontology and uses the whole-ontology collector, including ontology-level and
nested annotations. This is deliberately distinct from §5.8.1 declaration
typing, which considers the axiom closure. Each ontology/version header must
avoid the reserved namespaces. Each typed entity occurrence in a reserved
namespace must have precisely the built-in role of its IRI. Unknown reserved
terms and reserved named individuals are rejected. Untyped annotation IRI
values, import document addresses and facet IRIs are excluded from entity uses;
facet constraints and import processing have separate requirements.

`reserved_iri` recognizes all byte spellings starting with the four exact
Table 2 namespaces. `entity_iri_allowed` composes this with the independently
specified 49-entry built-in table. The proof gate checks the Rust constants and
Lean byte lists against the reviewed prefix inventory. Four public theorems
prove prefix/role recognition, total raw-ontology checking and acceptance iff
`VocabularyOK` holds on the original headers/entity uses. Diagnostics identify
the ontology header first, then version header, then the first forbidden entity
occurrence in the collector's specified order.

The distinction matters: declaring `owl:Thing` as an object property passes
generic class/property punning constraints, but the reserved-vocabulary check
rejects its object-property role. Ontology annotations need no axiom-closure
declaration solely by being ontology annotations, yet their properties still
must obey reserved-vocabulary restrictions. Both cases have actual-AST
regressions. The reviewed rules are [OWL 2 Structural Specification
§2.4, §3.1 and §5.1–5.6](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/).

This check does not establish IRI/UTF-8 validity, complete import closure,
literal/facet admissibility, acyclic custom datatype definitions, global role
restrictions or complete normalization. It is a separate checked entry point;
`check_ontology_typing` does not automatically invoke it. Neither result is a
`ValidatedOntology` or a logical consistency answer.

## M4: semantic preprocessing

`rowl_kernel::prepare` implements three checked entry points:

- `canonicalize_assertion`: positive and negative inverse-property assertions
  swap their endpoints and use the forward property. This is idempotent.
- `lower_subclass`: `C ⊑ D` becomes a universal object-domain constraint `¬C ∪ D`.
  Every object must satisfy it, including unnamed objects. Other axioms are
  retained verbatim; this is an internal prepared constraint, not a serialized
  canonical OWL axiom.
- `prepare_axiom`: compose both stages and retain annotations verbatim.

The corresponding total-correctness theorems establish exact satisfaction
equivalence for every interpretation over arbitrary object/data domains.
`preparation_preserves_anonymous_models` lifts that equivalence through OWL's
existential anonymous-assignment model condition. These stages introduce no
fresh named individuals, which matters for keys. Source ontology, declarations,
vocabulary and provenance must be retained by the eventual snapshot pipeline.

Example: an inverse hasPart assertion from motor1 to pump1 becomes the forward
hasPart assertion from pump1 to motor1. Machine ⊑ Asset becomes a constraint
satisfied by every object: it is outside Machine or inside Asset. Neither
operation alone performs an OWL query or establishes DL validity.

The meanings follow [Direct Semantics §§2.2–2.4](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/).
Full normalization, role preprocessing, AST-to-table composition and their
integration proofs remain M4 work.

## M4: ordered batch preparation

`rowl_kernel::batch::prepare_all` consumes a `SourceAxioms` list. Each occurrence
carries an `AxiomOrigin { document, ordinal }` and an annotated raw axiom. It
applies the existing preparation operation to each occurrence, retaining every
origin and annotation in the same order. Duplicate occurrences and duplicate
origin tags are retained; this is not a set canonicalizer or deduplication step.

`prepare_all_total_correct` proves totality and a pointwise `Corresponds`
relation, including exact satisfaction equivalence for arbitrary object/data
domains. `prepare_all_preserves_layout` proves the full origin/annotation lists
and length are unchanged. `prepare_all_preserves_models` proves model
equivalence for the entire source batch through the existential anonymous
assignment condition. No fresh individuals or changed vocabulary are introduced.

The origin fields are supplied metadata. The theorem proves their preservation,
not that they identify a real document location or match parsed bytes. Verified
parsers must later establish that link. Full structural/global validation,
normalization, role automata and reasoning remain separate work.

## Verification boundary

Both kernel and frontend are freshly extracted on every verification run.
Generated files are compared byte-for-byte and source hashes cover both crates,
the proof modules, registry and coverage gates. The combined audit also detects
cross-crate generated-name collisions. Only the previously accepted Lean logic
axioms and pinned toolchain/primitive-model TCB remain; no project semantic axiom
or admitted proof is introduced. Mathematical termination does not guarantee
that a physical machine has sufficient stack or memory.

## M3: complete IRI lexical grammar from bytes

`regular::matches_utf8` accepts an owned expression with empty language, epsilon,
code-point intervals, alternatives, concatenation and finite Kleene repetition.
It scans the entire input using the proved strict UTF-8 decoder. `Matched(false)`
means valid UTF-8 outside the supplied language; `MalformedUtf8` identifies the
first invalid unit. A grammar mismatch never suppresses a later encoding error.
It imposes no XML-character policy and performs no normalization.

`Rowl.Regular.Denotes` defines an independent mathematical word language using
union, language multiplication and Kleene closure. Nine public proofs cover exact
copying, empty-word recognition, three smart-constructor language laws, derivative
correctness, total byte matching and both acceptance/error equivalences.
`Utf8From` consumes precisely all bytes; `Utf8Failure` describes the first failed
unit. Completeness uses unique decoding and proves that success and failure cannot
both describe the same input. Recursive matching decreases the remaining byte
count even when the derived expression grows. Physical allocation/stack limits
and a performance bound are not established by this mathematical termination.

`iri::validate_iri` and `validate_reference` compile the entire RFC 3987 section
2.2 grammar into these expressions. The independent Lean grammar spells out all
productions, including all nine IPv6 forms, embedded IPv4, IPvFuture, user info,
ports, paths, queries, fragments, percent escapes and Unicode intervals.
Private compiled builders are proved against those languages; seven public
theorems establish exact bounded repetition, both compiled grammars, total
byte entry points and acceptance iff the normative languages hold. The RFC ABNF
uses case-insensitive literal v in IPvFuture, so V is also accepted. The `IRI`
production permits a fragment, as OWL/RDF IRIs require; the RFC's separately
named `absolute-IRI` production would omit it and is not substituted here.

For example, `cargo run -p rowl --example iri` accepts a pump's absolute IRI and
a Unicode IRI, rejects a broken percent escape, distinguishes `../motor` as a
relative reference and diagnoses a malformed UTF-8 unit. Regression tests use
an independent word-splitting language oracle, all IPv6 compression positions,
embedded address cases and Unicode/private-character boundaries. The functions
borrow and preserve the exact input bytes. They do not resolve a base, expand
prefixes, normalize spellings or impose scheme-specific network policy. They
are now used by the experimental N-Triples reader/writer. Composition into
its full correctness proof, OWL term parsing and the raw-ontology checker remains pending.

References: [RFC 3987 section 2.2](https://www.rfc-editor.org/rfc/rfc3987#section-2.2),
[OWL IRI identity](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#IRIs),
and [RDF 1.1 IRIs](https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/#section-IRIs).

## M4: complete anonymous positional restrictions

`anonymous::class_positions_allowed` rejects anonymous individuals in every
nested nominal/value position. `axiom_positions_allowed` covers the logical
body of all 37 axiom forms. `annotated_axiom_positions_allowed` also traverses
recursive annotations on the four axiom types whose whole contents prohibit
anonymous occurrences. Annotation values on other axiom types remain permitted.
This follows the literal occurrence scope of
[Structural Specification §11.2](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#The_Restrictions_on_the_Axiom_Closure).

Independent `ClassAllowed`, `AxiomAllowed`, `NoAnonymousAnnotation`,
`AnnotationPositionsAllowed` and `AnnotatedAllowed` definitions state these
conditions. Actual Rust traversal and closure scanning are proved total, and
acceptance is equivalent to the full positional predicate. Failure retains the
original first annotated axiom. Structural size and remaining-vector length
establish termination without arbitrary fuel. Nested annotation regressions
cover each prohibited axiom type, with permitted annotations on other types.

## M4: anonymous assertion graph forests

`anonymous_graph::collect_edges` projects positive anonymous-to-anonymous
object assertions from the complete supplied raw closure, retaining order,
orientation and repetitions. `AnonymousIndividual.scope` and `.label` are raw
byte vectors. `same_individual` compares both fields independently, and its
key is proved injective on the actual structural type. Distinct scopes are a
syntactic distinction, not an assumption of different logical denotations.
Parser/import assignment of the scopes is still a separate proof obligation.

`connected` decides undirected reachability by recursively removing an edge:
a walk either avoids that edge or can be shortened to cross it once in either
direction. Its exact totality proof restores the original graph. This initial
implementation may take exponential time; no performance promise is made.
`check_edges` and `check_forest` reject self edges and undirected cycles.
Repeated endpoint pairs contribute a single graph edge, regardless of property
or annotation spelling. The separate edge-multiplicity decision below counts structurally distinct
annotated assertions; graph-edge deduplication alone cannot decide that rule.

`Forest` independently requires loop freedom and Mathlib's absence of cyclic
walks. The Rust checker accepts iff this predicate holds. Its non-forest
outcomes retain actual input endpoints. An audited theorem connects accepted
graphs to connected components that are trees. The graph's full key carrier
also includes isolated keys; only endpoints of actual positive assertions have
edges, so other anonymous occurrences cannot introduce cycles.

Regressions cover separately allocated identical occurrences, document scopes,
reversed and repeated edges, cycles, self edges, excluded negative/annotation
assertions, and all 1,024 undirected graphs on four vertices against a separate
component-merging oracle. Forest acceptance alone neither accepts an illegal
negative assertion nor settles the separate multiplicity or named-boundary rules.

The named-boundary rule will follow the normative text. Its adjacent family
example appears to violate that literal rule; the discrepancy and selected
interpretation are recorded in [architecture.md](architecture.md). The forest
checker is independent of this boundary issue. Complete DL validation,
canonical imports, full parsing and executable OWL reasoning remain pending.

## M4: structural assertion equality and anonymous edge multiplicity

`assertion_equality` compares the actual raw literal, value, individual and
property types. Byte spelling and type tags remain exact; logical individual
or datatype-value equality cannot substitute for structural identity.
Literal lexical fields now share the byte representation already used by the
frontend. The independent datatype-map interface requires admitted lexical
forms to satisfy its Unicode UTF-8 grammar, and a checked semantic consequence
prevents a valid vocabulary from including malformed raw literal encodings.
These are representation conditions, not the normative datatype implementation.

`same_annotation` compares property, value and recursively nested annotation
sets. `same_annotation_set` uses mutual membership; association order and
repeated equivalent members do not matter. Nesting and all atomic fields do.
The independent recursive `AnnotationEq` relation is proved reflexive,
symmetric and transitive, and `AnnotationSetEq` is an equivalence relation.
Actual comparisons terminate by structural size and remaining-vector length.
Regressions include a matrix of nested annotations checked against a separate
ordered-set canonical-form implementation.

`same_object_assertion` compares positive object assertions and their metadata.
Logical fields remain ordered; inverse expressions are distinct structural
forms. The [structural specification](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Structural_Specification)
includes annotations in axiom identity. The checker does not extend this
comparison to all class expressions, data ranges or other axiom forms yet.

`anonymous_multiplicity::check_multiplicity` scans all pairs in the supplied
complete raw closure. `SamePair` identifies an undirected anonymous endpoint
pair; `Conflict` identifies two structurally distinct assertions on that pair.
`Restriction` independently states that all such members must be equivalent.
Totality, exact acceptance and actual conflicting annotated inputs are proved.
Equivalent repeated input occurrences are accepted without trusting caller
canonicalization flags. Different properties, inverse forms, orientations and
annotation sets are rejected when they share the anonymous edge.

The regressions specifically distinguish `p(a,b)` from `inverse(p)(b,a)`:
these can have the same logical meaning while remaining structurally distinct
axiom members. The validation stage must therefore precede inverse-assertion
lowering. Forest validity is independent: a triangle can pass multiplicity, and
different assertions on one pair can pass the graph forest condition.

Named-boundary validation is the remaining anonymous-graph condition. Canonical
scope assignment, parsing/import composition, general structural canonicalization
and the complete DL validator remain pending.

## M3: UTF-8 encoding, language tags and experimental N-Triples

`encoding::encode` returns one fixed-size UTF-8 unit or None for an invalid
u32 scalar. Five proofs establish exact scalar recognition, total canonical
encoding, None iff non-scalar, independent strict RFC-byte recognition of the
same value/width, and composition with the actual decoder at byte zero.
No replacement characters, truncation or allocation assumptions are used.

`langtag::grammar` builds the entire RFC 5646 ABNF from regular-language
operations. The independent `WellFormedLanguage` contains normal tags,
private-use tags and all 26 grandfathered tags. Private helper proofs cover
bounded repetition and ASCII-insensitive word compilation. Three public proofs
establish exact grammar denotation, total byte checking and acceptance iff the
independent grammar holds on the strictly decoded input. RFC §2.2.9 well-formedness
is syntax; registry validity and duplicate-variant/singleton restrictions are
separate and are not wrongly imposed on RDF language tags.

`ntriples::read` and `write` are experimental runtime operations, with explicit
errors/budgets and a low-level caller-supplied document scope. All semantics-changing
operations are extracted from Rust without unknown externals. Their full grammar,
byte-to-graph, blank-scope and serialization-isomorphism proofs are still pending.
The 68-case W3C syntax corpus and positive graph roundtrips pass. Details, exact
corpus hashes and the real maintenance CLI example are in [formats.md](formats.md).
This addition does not supply an OWL RDF-to-structural mapping or finish M3/M4.


## M3: complete byte-to-blank-token proof and shared scanner stages

`verification/Rowl/NTriples.lean` adds sixteen audited public theorems over
actual extracted Rust operations. The specifications use independent strict
UTF-8 unit relations, normative codepoint predicates and inductive maximal
scans. They do not define acceptance by calling the implementation.

The composed `blank_total_correct` and `blank_accepted_iff` establish the whole
`ntriples::blank` operation from a starting source byte to an RDF blank token:

- `_:` punctuation and a legal first PN_CHARS_U or ASCII digit;
- every one of the fourteen PN_CHARS_BASE intervals and the complete
  PN_CHARS suffix, with arbitrarily many internal dots;
- maximal scanning that backtracks exactly over trailing dots;
- exact original label bytes and verbatim caller-supplied scope, including
  opaque scope bytes, with no accidental identity changes;
- termination, bounded/nondecreasing label offsets and exact byte-budget
  overflow, without index/arithmetic failure in the proved bounded copy stage;
- only specified errors for punctuation, required EOF, malformed UTF-8,
  invalid first characters and resource limits.

The shared scanner proofs cover exact unit reads, required/expected-character
reads, comments and both whitespace modes. Comment scans stop before EOL or
exactly at EOF; malformed comment text diagnoses the first invalid unit.
Trivia acceptance is proved in both directions and keeps EOL handling confined
to the appropriate mode. Hashes inside quoted/IRI tokens are not consumed as
comments by the surrounding runtime reader.

`append_encoded_total_correct` accounts for one through four encoded bytes and
every intermediate budget cutoff: the private buffer contains exactly the
prefix that fits, and success is equivalent to fitting the whole unit.
`copy_term_total_correct` preserves exactly a bounded source span and diagnoses
oversized spans at the starting source byte. These support the upcoming
quoted-token composition rather than assuming string conversion correctness.

The new regression cases exercise comment Unicode/error offsets, CR/LF
boundaries, token-internal hashes, every PN_CHARS_BASE endpoint and the gaps
between intervals, non-UTF-8 opaque scopes, repeated blank identity and
internal/trailing dots. All 83 ordinary Rust tests and the external 68-case W3C
N-Triples syntax corpus pass; formatting, Clippy, actual-source extraction,
Lean checking and per-declaration axiom audits pass.

This completes the blank-token proof block, not the full N-Triples format or
M3. Quoted IRI/string tokens, language/datatype literal
construction and bounded whole-document-to-graph composition are now proved
in later sections. Writer isomorphism and
canonical imported document scopes still need proofs. All other required
formats and the OWL RDF mapping remain pending. M4's global role restrictions,
anonymous assertion multiplicity/named-boundary checks, datatype-definition dependency restrictions,
complete canonicalization and integrated validation remain pending. No full
ValidatedOntology API or OWL reasoning guarantee follows from this token proof.


## M3: full UCHAR/ECHAR escape payload proofs

Six further audited public theorems prove the actual `unicode_escape` and
`escape` operations. A shared Rust UCHAR helper covers both four- and eight-digit
forms. Its independent `HexDigits` relation uses natural numbers and exact
strict-UTF-8 unit positions; it does not call the Rust loop. The accumulator
invariant proves every step fits in u64, including `FFFFFFFF`, before scalar
validation rejects non-Unicode values. Surrogates and values above U+10FFFF
produce the original InvalidEscape offset rather than wrapping or replacement.

`unicode_escape_total_correct` and `unicode_escape_accepted_iff` establish total
execution and exact value/offset acceptance for payload counts bounded by eight.
The normative callers use exactly four/eight. Hex digits are not greedily
consumed. `HexError` accounts for the first required EOF/malformed unit, a
non-hex character or the final non-scalar value; valid productions cannot take
any of those error paths. The progress theorem establishes bounded advancing
source offsets for positive digit counts.

`escape_total_correct` and `escape_accepted_iff` compose marker reads with UCHAR
and all eight ECHAR productions. IRI mode admits UCHAR only. Every accepted
payload yields a Unicode scalar and a bounded advancing original source offset.
The payload function starts after a backslash supplied by its caller; it does
not itself inspect that backslash byte. The upcoming quoted-token proof must
establish that connection and compose delimiters, canonical encoding and output
budgets. Its raw-character scalar foundation is now proved directly from the
independent strict UTF-8 byte grammar.

The Rust quoted-character stage has been factored into `quoted_item` so raw and
escaped characters share one composed path. This refactor does not establish a
whole quoted-token proof. Two additional regressions check Unicode/scalar
boundaries, surrogate/max-u32 rejection, exact digit counts, malformed/truncated
payload offsets, IRI-mode ECHAR rejection and every cutoff inside three four-byte
characters, both raw and escaped. All 85 ordinary Rust tests and the external
68-case W3C suite pass. The full N-Triples graph parser/export proofs, required
other formats, OWL mapping and full M3/M4 exit criteria remain pending.


## M3: whole quoted tokens, IRIREF and RDF subjects

The actual extracted `quoted_item`, `quoted` and `read_iri` functions now have
composed total-correctness and complete-acceptance proofs. The independent body
relation ends at the first raw closing delimiter; an escaped delimiter remains
part of the value. Each item must either be a permitted strict UTF-8 source unit
or include an actual backslash followed by a complete permitted escape. Returned
bytes concatenate independent canonical RFC 3629 units. Encoder grammar
uniqueness and `encode_some_iff` connect every grammar-legal unit to the real Rust
encoder, instead of defining grammar acceptance by calling that encoder.

The body proof decreases the remaining source length. The source position always
advances and stays bounded, including when four/eight escape digits occupy more
bytes than their decoded value. The output invariant accounts for the caller's
byte budget. If a decoded unit cannot fit, the caller rejects at its original
source position and exposes no partial successful token. Exact failure relations
cover opening mismatch, EOF, malformed UTF-8, forbidden raw characters, invalid
escapes and resource limits; the encoder's non-scalar error branch is unreachable
from a valid raw/escaped item.

`read_iri` additionally composes the proved RFC 3987 absolute-IRI recognizer. It
preserves the decoded spelling without normalization, and accepts iff the full
IRIREF token, output budget and decoded absolute-IRI grammar hold. The actual
`subject` function then composes IRIREF and the previously proved caller-scoped
blank token. It accepts exactly those two RDF subject kinds and preserves the
exact IRI spelling or blank scope/label.

The ten new N-Triples theorems and two encoder theorems are in the exact-source
audit registry. Literal language/datatype suffix construction, triple grammar
and bounded whole-document parsing are now proved in the later section.
Parser-assigned scope composition across imports, graph export isomorphism,
other serializations and OWL mapping remain separate proof obligations. Neither M3 nor the byte-to-answer release criterion is complete.

## M4: top data property occurrence restriction

The new `topdata::axiom_allowed` and `topdata::check_axioms` operations implement
[OWL 2 Structural Specification §11.2](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#The_Restrictions_on_the_Axiom_Closure)
on the supplied raw axiom closure. Only a `SubDataPropertyOf` superproperty
position admits the top data property. The subproperty remains checked, including
when both operands spell the top property. Exact bytes determine the reserved
property identity; case changes and longer prefixes do not silently match it.

The implementation reuses the already proved complete entity-occurrence
collector. It checks every typed data-property occurrence in all other axioms,
including declarations, deeply nested class restrictions, key lists and positive
or negative data assertions. Annotation IRI references are preserved as
references rather than treated as typed data-property uses. The pure Lean
restriction is defined on the independent occurrence relation, not on the
executable checker's Boolean result.

Three new theorems prove the actual axiom operation total, the closure scan total
with the exact first offending annotated input, and successful closure acceptance
iff every supplied axiom satisfies this restriction. Three regressions cover
all six data class-expression forms, nested unordered members, keys, assertions,
exact spelling and identity-preserving first diagnostics. The maintenance Rust
example demonstrates an allowed faultCode-to-top hierarchy axiom and a rejected
functional top data property.

This is one global DL condition. Callers still supply the complete axiom closure;
role simplicity/regularity, datatype-definition restrictions,
canonical structure and complete validation/normalization remain pending. The
release ledger retains those obligations and `release_ready = false`.


## M3: complete language-tag tokens

The actual `tag_word`, `tag_tail` and `tag` operations now have source-linked
proofs. The independent maximal word relation distinguishes the ASCII-letter
head from later alphanumeric subtags. A hyphen requires a nonempty subtag; EOF
or an unmatched decoded character ends a valid suffix without consuming the
character. Malformed UTF-8 is diagnosed at its exact first source unit. Both
recursive scanners terminate by strictly decreasing remaining source length.

The full token proof includes the actual @ marker, a nonempty head, maximal
suffix, exact byte-span copying, output budget and the already checked RFC 5646
well-formed-language recognizer. It preserves original tag case. The independent
failure relation distinguishes an absent head, empty subtag, malformed unit,
copy-budget overflow and RFC grammar rejection. The copied-byte limit error is
at the spelling start after @; grammar errors identify @. No partial successful
token is returned. Token acceptance is proved in both directions, and every
accepted token advances within its original source.

Seven theorems and eleven semantic definitions are added to the registry. One
new Rust regression checks tag case, exact limits, empty subtags, malformed
UTF-8 positions and the specified ordering of budget/grammar failures. The full
literal operation and bounded whole-document/count composition are now proved
in the following section. Export and ontology mapping remain pending.


## M3: complete bounded N-Triples document reading

The actual Rust literal operation now binds exact decoded lexical bytes to
xsd:string when no suffix exists, the original well-formed language tag after @,
or an exact absolute datatype IRI after ^^. Explicit rdf:langString without a
language tag is rejected even when its spelling uses Unicode escapes. The
implicit xsd:string constant is not charged as a source term. The literal and
object operations have totality, complete acceptance and bounded progress proofs.

`read_triple` composes the actual subject, predicate, object, maximal horizontal
trivia/comments, required period and EOF/EOL boundary. Every accepted triple
strictly advances within the original source. `read_with_limits` now composes
leading trivia and the complete document loop. Its independent `Document`
relation preserves ordered raw occurrences, including duplicates; repeated
blank labels keep the exact caller-supplied scope and label. The reader preserves
all and only those specified triples. Both public bounded reading and the
input-sized-default `read` have total-correctness and acceptance-iff theorems.

The document loop terminates by decreasing remaining source length. Its
accumulated occurrence count is bounded by the current byte position, proving
vector-push capacity in the translation model without an unproved allocation
assumption. The requested count limit is checked only after a complete triple;
a malformed next triple therefore retains its earlier syntax error at a full
count boundary. The failure relation covers each first parsing/trivia/budget
stage with its exact original offset. No failure exposes a successful partial
graph. `document_count_bounded` proves the accepted count respects the limit.
Physical memory/stack failures remain outside this mathematical execution model.

This adds 19 public theorem audits and 28 semantic-definition audits. Two Rust
regressions check literal kinds and escaped rdf:langString, implicit-datatype
budget behavior, shared blank identity across lines, malformed document suffixes
and first-error/count-limit ordering. The independent productions are reviewed
against the pinned N-Triples Recommendation and RDF 1.1 literal requirements;
Lean proves the code matches those productions, not the English standard itself.

The writer still needs grammar, totality, output-budget and parse-after-write
blank-isomorphism proofs. Canonical blank scopes across imports, RDF-to-OWL
mapping, the OWL 2012/RDF 1.1 literal bridge and the other required serializations
remain separate M3 obligations. Full M3 and M4 completion claims are unchanged.


## M4: complete raw role facts

`rowl_kernel::roles` now traverses actual class expressions, annotated axioms
and the complete supplied axiom vector. Role records borrow the original IRI
and carry an explicit inverse-orientation flag. Conversion preserves the
original value; inversion changes only the flag, and actual double inversion
is proved to return the original role. No lexical normalization, symbol IDs
or caller-supplied role metadata are introduced.

The output retains five independent occurrence lists:

- Nodes: each explicitly typed object-property occurrence supplies p and INV(p),
  including declarations and nested class/axiom uses. Untyped annotation IRIs
  and punned class/datatype roles do not produce object-property nodes. Exact
  membership iff the full collected AST contains that object-property IRI is proved.
- Hierarchy edges: single subproperty edges; both directions for every distinct
  equivalence-list occurrence pair; inverse-property edges; symmetry edges; and
  each edge's inverse orientation. Chains contribute no ordinary hierarchy edges.
- Composite seeds: transitive expressions and chain superproperties in both
  orientations, plus the exact direct top/bottom object-property expressions
  appearing in typed object-property positions, following §11.1's definition.
- Simple-role requirements: all nested cardinality/self property fields and
  functional, inverse-functional, irreflexive, asymmetric and disjoint-property
  axiom fields. Qualified fillers are traversed. An existential/universal/value
  property, key-list property, reflexive property or domain/range property does
  not gain this requirement merely from that position; nested restricted class
  expressions still do. Zero cardinality has no restriction exemption.
- Chains: the original minimum-two ordered property list and original
  superproperty expression. Nothing sorts, reverses or lowers chain operands
  before the eventual regularity proof.

The independent `Correct` and `ClosureCorrect` definitions specify exact
ordered output values, not merely subsets of expected names. Totality proofs
cover every raw class and axiom form, all nested fillers, all list members,
repeated occurrences and empty input. Closures retain their supplied order.
The linked owned output avoids an unproved vector-growth bound; each indexed
source traversal proves its index increment safe from the source vector bound.
Physical allocation/stack limits retain the documented TCB/execution scope.

Nine public theorem audits and 30 semantic-definition audits are added. The independent global hierarchy, reachability, composite, simplicity and chain-order predicates state the next validator targets. The collector is proved to supply exactly the hierarchy edges and composite roots. These predicates alone do not implement their decisions. Four
Rust regressions cover ordered chain references and original pointer identity,
all n-ary equivalence pairs and inverse orientations, nested simple-role
requirements without accidental broad restrictions, exact typed built-in
spellings, repeated occurrences, empty closure and inversion.

These are role preprocessing facts. They do not yet compute reflexive-transitive
hierarchy reachability, accept/reject the simple-role restriction, find the
strict order required for chain regularity, or establish full DL validity.
Reachability and the simple-role decision are now completed in the following section; chain regularity and full DL validity retain their release obligations. The normative source is
[Structural Specification §11.1–11.2](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Property_Hierarchy_and_Simple_Object_Property_Expressions).


## M4: composite reachability and simple-role decision

`roles::non_simple_closure` computes finite multi-root reachability using an
owned worklist. It tolerates repeated roots/nodes/edges and cyclic hierarchies,
without fuel. Each new key removes one available node; skipped seen keys remove
one pending task. Lean proves termination by that lexicographic measure, exact
reachable-key membership, duplicate-free output, and a genuinely reached absent
key if the externally supplied universe is incomplete. Complete generic output
is possible iff every reached key is present. Exact role equality compares the
original bytes and orientation, including separate allocations of equal IRIs.
Owned contains/successor traversal is proved to restore its input exactly;
this avoids unsupported nested shared borrows in the pinned translator.

`roles::classify_non_simple` derives the graph from the actual raw axiom vector.
Independent structural proofs show every composite root and every hierarchy
target belongs to AllOPE. Consequently its missing-node outcome is impossible,
and its output is exactly the non-simple properties of the supplied closure.
No caller supplies classification flags or trusted numeric role metadata.

`roles::check_simplicity` checks all collected restricted uses and returns
Allowed iff `SimpleRestriction` holds. ForbiddenRole carries the original IRI
and orientation at the first failing occurrence in closure/nested syntax order;
the proof gives an exact prefix of earlier simple requirements. MissingNode
is excluded for this raw entry point. Allowed certifies only this restriction.
For example a transitive hasAncestor below hasRelative makes a nested inverse
zero-cardinality restriction on hasRelative forbidden. A chain's operands do
not become non-simple merely by occurring in the chain; unrestricted existential,
reflexive and key-list uses do not acquire a simplicity requirement.

Six public theorems and three independent definitions are added. Five Rust
regressions cover cycles, inverse propagation, exact identity, repeated and empty
roots, genuinely missing reachable nodes, ignored unreachable endpoints, nested
first-error identity and permitted versus forbidden role uses. Physical
allocation/stack failures remain outside the mathematical execution model.
Canonical import assembly, chain-order regularity and the remaining global DL
restrictions retain their separate release obligations.


## M4: complete property-hierarchy regularity decision

`role_order::check_regularity` now decides the full 2012 Structural Specification
§11.2 property-hierarchy restriction on the supplied complete raw axiom closure.
The independent `Rowl.Roles.Regular` predicate retains the literal published
inverse-source condition on property names. No stronger inverse-target
invariance or role-equivalence preprocessing is silently substituted.

The chain compiler makes a deterministic forced dependency list. Direct top
superproperties and exact two-occurrence self-transitivity need no dependencies.
A self occurrence at the first endpoint selects the remaining operands; otherwise
a last self occurrence is omitted. Other operands remain in order. Lean proves
that, for any irreflexive ordering, these constraints hold iff one of the five
independent `ChainOrdered` alternatives holds. A middle self occurrence or both
recursive endpoints in a longer chain introduces a self-dependency. The proof
justifies this reduction rather than assuming an informal cycle heuristic.

`role_order::close_order` computes the least relation containing those constraints
and closed under transitivity and inversion of a source when its target is a
direct property. The finite Cartesian pair universe permits duplicates; output
contains each derived pair once. The available-pair/pending-task lexicographic
measure proves termination without fuel. Frontier invariants cover seeds,
all compositions of resolved pairs and inverse-source consequences. Totality,
exact derived membership and generic completeness iff every derived pair lies
in the supplied universe are proved. Owned pair/list operations restore their
inputs exactly, without unsupported shared-reference assumptions.

Raw-AST chain/nodes composition proves every required or derived pair is in
AllOPE × AllOPE, including inverse sources. `least_chain_order` therefore cannot
return MissingPair. The final checker uses actual hierarchy reachability from
the superproperty back to the subproperty for each candidate strict pair. Those
queries are also proved complete and cannot lose a raw node. Regular returns
the exact concrete ordering; its strictness, transitivity, inverse condition,
chain conditions and hierarchy compatibility are proved. HierarchyConflict
identifies a forced pair contradicted by ordinary hierarchy reachability. Every
permitted order contains the computed closure, so this is a proof that no such
order exists. `check_regularity_accepted_iff` connects actual success to existence
of a witness for `Regular`; both missing outcomes are excluded.

Ordinary subproperty cycles alone are permitted by this restriction when no
chain forces a conflicting strict pair. Recursive endpoint chains, exact
transitivity and direct top exemptions pass. Tests reject middle/long double-end
recursion, cross-chain cycles, reverse ordinary hierarchy paths and conflicts
introduced by the inverse-source rule; the W3C family-chain example returns a
concrete relation including derived transitive pairs. Seven new Rust regressions,
ten public theorem audits (including two chain-conversion/top helpers and the
hierarchy-target presence law) and ten independent definitions are added.

This completes the simple-role and property-hierarchy regularity obligations,
not M4 as a whole. Canonical structural validation, datatype restrictions,
full normalization, automata and their remaining proof links
still require implementation. Full imports and other byte frontends remain M3.
The finite prototype uses linked recursive lists and recomputes hierarchy queries;
performance optimization and physical allocation/stack resource handling retain
their separate milestones. Mathematical totality uses the documented execution
model and pinned trusted computing base.


## M4: named boundary and complete anonymous restriction composition

`anonymous_boundary::check_boundary` now checks the normative §11.2 condition:
each anonymous tree must have some vertex incident to at most one structurally
distinct positive object assertion with a named endpoint. Either orientation
counts. Properties, annotation sets, literal spellings and ordered body fields
remain part of the assertion identity; equivalent occurrence copies count once.
The adjacent informative family illustration conflicts with the literal rule;
ROWL follows the normative condition, as recorded in architecture.md.

The actual first/second endpoint projections cover every positive anonymous
endpoint, without trusting a caller vertex list. Named incidence and the
at-most-one structural bound are proved exact. The component search composes
the proved undirected connectivity operation and scans both endpoints of every
raw positive assertion. Owned graph inputs are restored exactly. Every index
step is proved bounded and advancing; recursion has no heuristic fuel.

The completeness proof establishes that every graph edge endpoint occurs in
the finite candidate scan, and reachability from a candidate stays within it.
Every omitted anonymous occurrence has zero named incidences and can witness
its own component condition. Hence the finite check is equivalent to the
independent condition over the full anonymous carrier, not merely a supplied
candidate list. A NoRoot outcome retains an original endpoint and proves that
every reachable anonymous vertex violates the bound. Forest validity remains
separate in this operation; on accepted forests these components are precisely
the normative trees.

`anonymous_restrictions::check_anonymous` composes positional validation,
forest checking, edge multiplicity and the named boundary. Its own extraction
and proofs establish totality and success iff their independent conjunction.
Failure priority is positions, forest, multiplicity, then boundary. Each failure
retains original stage evidence, proves the conjunction fails and establishes
every preceding stage. Run this on the complete standardized-apart raw closure
before inverse-assertion normalization.

Eight public theorem audits and nine independent definitions are added, with
13 Rust regressions. These include 216 small graph/attachment configurations
against an independent reachability/component oracle, duplicate annotation-set
members, orientation/metadata/property distinctions, document scopes, isolated
occurrences and composed diagnostic priority. The maintenance example runs the
combined checker on an assembly/motor component and then adds named attachments
until it has no qualifying root.

All anonymous-individual §11.2 restrictions on the supplied closure are now
implemented with exact-source proofs. This completes that block, not full M4.
Canonical parsing/import scope assignment, general structural validation,
datatype restrictions, complete normalization/automata and OWL reasoning retain
their separate release requirements. Physical allocation/stack failure remains
outside the mathematical execution model.


## M4: complete data-range identity and datatype definition availability

`range_equality` compares every raw data-range constructor against an independent
recursive structural-equivalence relation. Intersection, union, literal and facet
associations are unordered sets; order and equivalent repetitions are ignored
at every nesting level. Datatype and facet IRIs, lexical bytes, constructors and
nesting remain significant. The comparator does not flatten unions, remove
complements or compare literal values. Annotated datatype-definition identity
also includes the defined datatype and recursive annotation-set equivalence.

The actual comparators have total-correctness proofs. Range equivalence is
reflexive, symmetric and transitive on all raw data ranges; definition equivalence
has those laws on actual definition axioms. Each recursive comparison decreases
structural size, and every vector scan is bounded and advancing. Seven regressions
include a 3,600-pair constructor matrix against an independent recursive set
representation. This remains structural comparison, not full AST canonicalization
or distinct-minimum-arity, facet or lexical validation.

`datatype_definitions::check_definitions` derives occurrences from the actual
complete supplied raw axiom closure, using the proved collector. This includes
literal and facet datatypes and recursively nested axiom annotations; ontology
annotations and untyped IRIs retain their separate positions. A custom datatype
must have one nonempty equivalence class of annotated defining axioms. Equivalent
copies count once, while distinct ranges or metadata count as separate definitions.
Predefined OWL 2 datatype names, including rdfs:Literal, permit no defining axiom.
The built-in name recognizer reuses the checked fixed 2012 declaration vocabulary;
it does not implement lexical or value spaces.

The extracted bounded searches and occurrence traversal are proved total.
Acceptance holds iff availability and structural uniqueness hold for every
actual datatype occurrence. A missing outcome preserves the original used IRI;
redefinition and conflict outcomes preserve original annotated axioms. Every
failure establishes rejection of this condition. Seven regressions cover recursive
occurrences, reordered definition copies, metadata distinctions, predefined
redefinition and the boundary that cycles or invalid lexical forms can still pass
this availability-only operation.

Sixteen public theorem audits and thirteen definition audits are added. The
maintenance example actually checks a missing SafeTemperature definition, adds
its decimal restriction and an equivalent reordered copy, then diagnoses a
conflicting definition and a predefined xsd:decimal redefinition.

This completes definition availability/uniqueness, not all datatype restrictions.
The normative dependency order, prohibition of custom datatypes in literals and
as restriction bases, complete datatype maps/facets/lexical spaces, import and
scope derivation and complete M3/M4/OWL reasoning remain release requirements.
Mathematical totality retains the pinned execution-model boundary; physical
allocation/stack failure has its own resource-handling milestone.


## M4: datatype dependency order and composed definition restrictions

`datatype_order::collect_dependencies` now derives the ordered smaller-to-defined
pairs from every datatype-definition range in the supplied complete raw closure.
The proved range collector covers all six constructors, including literal
datatypes in enumerations and facet values. Enclosing annotations and untyped
facet IRIs are outside DR and create no dependency. Every endpoint is proved to
be an actual typed datatype occurrence in the axiom closure; caller node metadata
is not trusted.

The actual directed reflexive reachability operation is proved total and exact,
including restoration of its owned graph. Each recursive call removes one edge.
A path either avoids that edge or can be shortened to cross it once. The separate
nonempty-path relation distinguishes a cycle from mere reflexive reachability.
The incremental checker rejects an original edge with a reverse path, including
self-dependencies, and permits repeated edges and directed diamonds. Its rejection
proves that no containing strict partial order exists.

Cycle freedom is proved equivalent to the existence of an irreflexive, transitive
relation containing the required pairs. Nonempty transitive reachability provides
the mathematical success witness. A separate checked carrier equivalence proves
that the order on actual occurring datatypes and an isolated extension to all IRI
values have exactly the same existence condition. The final raw-axiom operation
therefore accepts iff the normative §11.2 datatype dependency order exists.

`datatype_restrictions::check_definition_rules` composes the already proved
availability/uniqueness check with that order decision. Its totality and exact
acceptance cover their independent conjunction. Missing definitions, predefined
redefinitions and structurally distinct multiple definitions precede cycle
errors. A cycle result proves availability succeeded and preserves original
range/defined IRI endpoints. No semantic normalization happens before validation.

Ten public theorem audits and fourteen definition audits are added, with ten Rust
regressions. Tests include all 512 three-node directed graphs and their reachability
queries against an independent transitive matrix, complete range occurrence
projection, literal/facet dependency cycles, the W3C tax-number shape, self edges,
diamonds, duplicates, diagnostic priority and original borrowed evidence. The
maintenance example accepts a SafeTemperature → RecordedTemperature → decimal
reference chain, then changes it into a circular definition and actually receives
the composite Cycle result.

The two §11.2 datatype-definition conditions for the fixed reviewed OWL 2 names
are now implemented with exact-source proofs on the supplied complete raw closure.
This is not all datatype or DL validation: custom datatype literal/restriction
positions, normative lexical/facet/value spaces, canonical parsing/imports/scopes,
full normalization/automata and the full OWL reasoner remain release requirements.
The correctness-first directed path operation permits exponential running time;
physical memory/stack limits still require their separate resource milestone.


## M4: all defined-datatype positions and structural composition

`datatype_positions::defined_datatype` derives defined names from the actual
complete supplied definition closure, using exact IRI byte identity. Declarations
and unrelated IRI roles do not define a datatype; duplicates, metadata and the
position of the defining axiom do not change whether a definition exists. A
literal occurrence before its defining axiom is therefore still checked.

The independent positional specification covers all six range constructors,
all eighteen class forms, optional object/data cardinality fillers, every axiom
body form, data/negative/annotation assertion literals, enumeration and facet
values, and recursively nested enclosing annotation trees. Defined datatype
names remain permitted as named ranges. Literal datatype and restriction-base
positions exclude them exactly. This does not substitute value-space reasoning
for structural positions or claim lexical/facet validity for other raw literals.

Each actual traversal is proved total, and each bounded vector scan is advancing
and safe under the extraction model. The complete closure operation preserves
the first original forbidden annotated axiom and accepts iff all specified
positions obey the condition. The ontology operation checks every supplied
ontology annotation first, preserving the first original root annotation tree
on failure. An axiom failure proves those ontology annotations passed. Exact
ontology acceptance includes both independent conditions.

Imported ontology annotations must be supplied and checked separately against
the same complete definition closure. Checking only local definitions in an
import source would miss imported custom datatype names. Canonical import and
annotation assembly remains an M3 obligation; this API neither fetches documents
nor invents a complete closure from local annotations.

`datatype_restrictions::check_structural_datatypes` now composes definition
availability/uniqueness/predefined protection, dependency order and all supplied
positional conditions. Its own extraction and proofs establish totality and
success iff their independent conjunction. Definition availability and cycles
precede position failures; ontology annotations precede axiom positions. Each
failure retains original evidence and proves rejection; position failures also
certify successful definition rules.

Thirteen public theorem audits and sixteen definition audits are added, with ten
Rust regressions covering all range positions, nested data/object fillers,
positive/negative/annotation assertions, recursively nested metadata, supplied
ontology annotations, definitions after uses, original borrowed diagnostics and
composed priority. The maintenance example permits SafeTemperature as a property
range, rejects a literal typed with that defined datatype, then accepts its
structural positions when the literal is typed as decimal.

These are structural datatype conditions, not the normative datatype solver or
all DL validity. Undefined/empty-lexical built-in literal datatypes, concrete
lexical forms, facet admissibility, value-space membership and semantic datatype
reasoning still require M5. Full canonical structure/arity, declaration/global
composition, normalization/automata, byte-derived imports/scopes and the full OWL
reasoner remain release requirements. Physical memory/stack resource outcomes
remain outside the mathematical termination result.


## M4: all class-expression structural comparison and nonempty keys

`class_equality::same_class` now compares all eighteen standard class-expression
constructors. Class intersections/unions and nominals use unordered set
membership recursively; object property orientation, scoped individual identity,
exact literal spelling, numeric cardinality and constructor/nesting structure
remain significant. Every data form composes the already checked complete
six-form data-range or literal comparison. No logically equivalent expression is
silently substituted for a structurally different one.

Omitted object-cardinality qualifiers compare as the named `owl:Thing`; omitted
data-cardinality qualifiers compare as the named `rdfs:Literal`. This follows
[Structural Specification §§8.3 and 8.5](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Cardinality_Restrictions).
Only those exact named forms serve as defaults. A double complement of either,
a universal union, abbreviated IRI bytes and case variants remain structurally
different. Explicit recursive set members still retain nesting. Raw occurrences
are retained; this comparison does not produce canonical output or drop raw
operands before duplicate-disjointness validation.

The independent `Rowl.ClassEquality.ClassEq` relation is proved reflexive,
symmetric and transitive for every constructor, including arbitrary nested raw
repetitions and omitted qualifiers. The extracted actual Rust comparison and its
set/optional/atomic operations have total-correctness proofs. Exact unary-natural
comparison is also proved equivalent to mathematical natural-number equality.
There are twelve new audited public theorems and nine semantic definitions.
Four Rust regression tests include all 18 constructors checked pairwise against
an independent ordered-tree/standard-set oracle, all six omission defaults,
nested non-flattening, scope/property orientation and exact literal identity.

`keys::check_keys` separately checks the complete supplied raw axiom closure for
[the §9.5 nonempty-key rule](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Keys).
A key may use object properties, data properties, or both, but not neither.
Metadata cannot supply missing members. Totality and exact acceptance are proved;
failure retains the first original annotated axiom and proves all preceding
axioms passed this restriction. Three public theorems and three definitions are
audited, with three Rust regression tests. Length checks deliberately use the
supported pinned Vec model; unsupported `Vec::is_empty` extraction was rejected,
without adding external semantic assumptions.

These operations are exposed through the experimental Rust library and exercised
by the maintenance example. Distinct association arities, complete axiom
structural identity/canonicalization, byte frontends/import scopes, concrete
datatype reasoning and full DL validation/OWL decision procedures remain their
own open requirements. In particular, this supplies the nonempty structural
key check, not the NAMED key-inference algorithm. The M3/M4 full exit criteria
and full-language v0.1 target are unchanged.


## M4: complete raw structural arities and duplicate-disjointness validation

`arity::check_arities` now checks all structural association arities represented
by the complete standard unary raw OWL language. The independent specification
uses existential pairs of different structural equivalence classes for minimum-
two associations, rather than trusting the two written fields or using one
implementation-chosen anchor. Lean proves the actual anchor scan equivalent to
this pair specification using the checked reflexive/symmetric/transitive class
and range relations. Atomic data-property/object-property/individual identity
uses exact byte fields, orientation and standardized caller scopes.

Every data intersection/union, class intersection/union, EquivalentClasses,
equivalent object/data properties and SameIndividual requires two distinct
members after comparing recursively as sets. Repeated raw occurrences may remain
when that requirement is met. The nonempty nominal/literal/facet associations,
nonnegative cardinality values, unary standard data quantifiers and minimum-two
ordered property chains are enforced by the raw constructors. Ordered chains
may repeat; inverse-property axioms keep their ordered fields. No unique-name
assumption is introduced for interpretation of individuals.

The adopted [2014 correction proposal](https://lists.w3.org/Archives/Public/public-owl-comments/2014Apr/0000.html)
is now enforced on original raw members of DisjointClasses, DisjointUnion,
disjoint object/data properties and DifferentIndividuals. Pairwise structural
repetitions fail even when another different member is present. DisjointUnion's
defined class is outside that member association. Omitted versus explicit
cardinality defaults and reordered nested sets count as repeated members;
logically equivalent but structurally different expressions do not. This remains
the explicitly accepted compatibility decision, not an amendment to the 2012
Recommendation. The separately required RDF `x owl:disjointWith x` mapping and
its model-equivalence proof are still pending.

The actual traversal covers all 18 class forms, six data ranges and 37 axiom
variants, including optional fillers and every nested member. It composes the
proved nonempty key-property rule. Metadata neither changes arities nor supplies
missing key members. Success is proved exactly equivalent to the independent
whole-closure predicate. Failure keeps the first complete original annotated
axiom and proves all preceding axioms passed this stage. There is no fuel or
caller-supplied membership/equality table. Fifteen new public theorems and seven
semantic definitions are audited.

Eight Rust regression tests cover all affected association families, all five
disjoint/difference forms, default qualifiers, reordered nested sets, scope
identity, harmless repetition, recursive bad fillers, key/chain boundaries and
original annotation preservation. Exhaustive finite atomic sequences are compared
against independent standard-set counts at lengths two through five; positive
five-member uniqueness cases exercise complete nonempty tails. Raw lexical/facet
invalidity is deliberately outside this arity predicate and still needs its own
checks. This completes the raw structural arity obligation, not M3/M4 in full:
canonical output, all byte frontends/import scopes, concrete datatypes, remaining
composition/normalization and the OWL decision procedure still require work.


## M4: complete annotated-axiom structural comparison

`axiom_equality` compares all 37 standard raw axiom forms. This completes the
structural comparison families for atoms, annotations, data ranges, classes and
axioms; it does not yet construct canonical output. The independent `BodyEq`
relation explicitly covers every constructor, `SubPropertyEq` preserves singleton
vs chain structure, and `AxiomEq` includes the complete nested annotation sets.

Unordered class, property, individual and key associations use set membership;
reordering and equivalent repetitions do not change identity. Class members
retain the proved cardinality omission defaults. Chains retain ordered positions,
repeated occurrences and length. Fixed association fields remain significant,
including the two inverse-property fields. The normative UML Figure 14 calls
these objectPropertyExpression1/2 and marks the chain association ordered and
nonunique; Figure 18 gives separate unordered object/data key associations.
The comparator follows Section 2.1 of the Structural Specification, and makes no
semantic simplification such as merging logically equivalent reversed inverse
axioms, lexical value equivalents or flattened expression trees.

Eleven actual Rust entry points have total-correctness proofs. Nineteen new public
theorems and three semantic definitions are registered and audited: six laws
establish reflexivity, symmetry and transitivity for body and annotated identity,
and two compatibility theorems connect the existing positive-object-assertion
and datatype-definition restrictions to the full relation. Bounded vector scans
are proved without external equality assumptions. Entity kind, inverse orientation,
scoped anonymous identities and exact literal lexical/datatype fields are retained.

Six new Rust regression tests cross-check 111 fixtures (all constructors with
original, equivalent-reordered and changed variants) pairwise, and exhaustively
compare small property/data/individual associations with independent BTreeSet
membership and chains with list equality. Tests also cover empty key lists,
constructor/field distinctions, provenance nesting, blank scopes, lexical-value
lookalikes, and existing comparator agreement. The maintenance example compares
an imported inspection policy, a changed source annotation and reversed chains
using the actual new library calls.

Raw disjoint duplicates can compare as the same unordered structural association
while failing the separately proved arity rule. Arity validation must happen
before future deduplication; no canonical output, semantic congruence,
model-preserving whole-AST normalization, complete DL validity or OWL inference
is claimed by this comparison block. All remaining M3/M4 and release obligations
retain their existing status.


## M4: full structural semantic congruence

`StructuralCongruence` now connects the complete raw structural comparison
families to `OwlSemantics`, rather than assuming structural identity is logically
safe. Six new audited definitions and eighteen public theorems cover all six data
ranges, eighteen class-expression forms and thirty-seven axiom bodies, and lift
this result through annotated axioms to whole supplied standardized-apart closures.
No Rust reasoning or canonical-output algorithm is added by this proof block.

Range identity preserves denotation without interpretation side conditions.
Class identity requires `Defaults`, exactly the owl:Thing and rdfs:Literal
interpretation conditions needed for omitted cardinality fillers. These follow
from full IsInterpretation and survive anonymous reassignment. Explicit class and
data filler definitions avoid proof-dependent matches. Every recursive child is
proved smaller; intersection/union member sets use proved mutual matching, and
cardinality congruence preserves finite injections into any finite/infinite domain.

Axiom congruence additionally requires `DistinctMembers` for the five
occurrence-sensitive disjoint/different families, supplied by original arity
acceptance. Generic pairwise transfer uses original structural uniqueness and
relation equivalence, never unique denotations. AllEqual and key-member conditions
use set transfer, retaining named key subjects/fillers. Ordered chains preserve
relational composition exactly. Annotation/declaration meanings remain inert,
while full structural identity retains their metadata fields.

`compared_axioms_satisfaction` links successful actual Rust same_axiom and both
actual arity checks to satisfaction equivalence. `closure_satisfaction` and
`closure_models` permit reordered/repeated equivalent whole-axiom copies but
require both supplied closures to pass arity. The same anonymous assignment
witnesses both. `closure_model`, `closure_consistency`, `source_entailment` and
`target_entailment` quantify over each fixed datatype map/embedding/vocabulary
and arbitrary domains. Vocabulary derivation, actual canonical output, scope
assignment and normative datatype solving are not assumed to be implemented.

Three checked semantic regressions demonstrate necessary premises: repeated
DisjointClasses(Thing Nothing Thing) compares equal to its distinct-member
counterpart but differs in satisfaction; original arity rejects it. Arbitrary
interpretations with an empty named top class or top data range make omitted and
explicit cardinality fillers differ. A new Rust regression covers successful
comparison and failing original arity for all five duplicate-sensitive families.
The existing constructor/default/ordering regressions remain in the full suite.

All source-linked theorem and semantic-definition audits use the existing allowed
logical axioms only. This completes structural semantic congruence, not actual
whole-AST canonicalization, M3/M4 integration, a concrete datatype map, parsing or
a full OWL decision procedure. Their original release requirements stay pending.


## M4: actual validated outer axiom-set construction

The previous block proved structural semantic congruence. `axiom_set::build` now
uses it in an actual Rust operation over every complete annotated axiom form.
Twenty public theorems and ten independent definitions connect the extracted
constructor and all six public operations to exact mathematical contracts.

A complete supplied standardized-apart closure consists of original annotated
axioms plus caller document/ordinal tokens. The operation checks every original
arity before grouping. A repeated disjoint/different member therefore remains a
first-original failure even when another structurally equivalent copy would
pass after deduplication. Successful output borrows all original objects and
provides increasing first-representative indices and a full per-occurrence map.
Changing origin tokens does not change structural identity; changing annotations
can. Recursive metadata, class/data equivalence and omission defaults use the
proved full comparator. Property chains retain their order and repetitions.

The specification defines first representatives by minimality and roots by a
filtered mathematical range, independently of the Rust search and accumulation.
The scan terminates with an exact earliest match or its prefix boundary. Native
Vec pushes and arithmetic are proved within bounds. Every map entry denotes the
first structurally equivalent original, is at or before its source occurrence,
appears among the representatives and resolves idempotently. Representative
indices increase strictly and no two selected originals have equivalent full
annotated axioms. All public lookups terminate with exact original values or
None at out-of-range indices. Private Rust fields make the builder the only
constructor available to clients.

The selected closure contains actual original axioms, inherits arity acceptance
and matches the complete original structural set. Checked congruence composes
this with full Model/Consistent/Entails preservation under fixed datatype maps
and vocabulary, with arbitrary finite or infinite domains and anonymous
reassignment. Successful actual builds supply the invariants of these results.
No OWL decision or concrete normative datatype solver is introduced.

Five new regression tests cover all 37 axiom families against an independent
fixture-class oracle, empty/single inputs, exact pointer/provenance retention,
first-error priority, all five duplicate-sensitive families, ordered chains,
changed annotations, anonymous scopes and distinct lexical value spellings.
Shared fixture builders avoid maintaining a second version of the full axiom
comparison fixtures. The maintenance executable groups three policy occurrences
into two classes while retaining all document/ordinal records.

This completes outer structural axiom-set construction only. General duplicate-free
nested AST output, source-byte provenance and scope/import assembly, remaining
M3 parsers/mappings and complete M4 DL validation stay pending.


## M3: complete Functional Syntax names and prefix-table operations

Twelve public `Names` proofs establish exact grammar compilation and whole-byte
recognition for prefix/local names, abbreviated IRIs and node IDs. The independent
codepoint languages follow the referenced SPARQL 2008 productions. Malformed
UTF-8 suffixes remain visible after a lexical mismatch; scope assignment and
Turtle-specific escapes are separate work.

Nine public `Prefixes` proofs establish the actual complete table checker,
implicit namespace selection/copying, immutable source accessor, exact lookup
and bounded expansion. The independent specification uses list traversal,
unique-name predicates, byte grammar membership, mathematical concatenation and
lengths. Check acceptance is exactly every declaration's lexical/absolute-IRI/
reservation conditions plus unique names, and successful construction preserves
all original declaration bytes. Expansion accepts exactly grammatical parts,
a declared or implicit namespace, a fitting output byte limit and a valid final
absolute IRI. Typed failures preserve source/phase priority. No parser-supplied
lexical metadata is trusted by expansion.

Twelve regression tests use independent small-word grammar oracles, all Unicode
base interval boundaries, malformed suffix offsets, all four implicit bindings,
reserved/duplicate declarations, unused declaration validation, source pointer
retention, case/normalization distinctions, exact UTF-8 byte budgets and final
IRI counterexamples. `cargo run -p rowl --example prefixes` expands real
maintenance vocabulary names and demonstrates missing-prefix and output-limit
outcomes. It does not execute OWL inference.

The broader Functional Syntax parser and combined prefix/relative-IRI ledger
entries stay pending; other serializations, import scope/provenance assembly,
M4 composition and the full OWL reasoner remain release requirements.


## M3: exact greedy regular-language prefix matching

The next lexer component is the actual `longest::longest_prefix` byte operation.
Three public theorems and four audited specification declarations prove
termination, exact greatest matching byte endpoints, complete acceptance and
source endpoint bounds. Independent canonical UTF-8 segments and language
membership define every eligible endpoint. The mathematical maximum distinguishes
no match from a zero-width match. An accepted prefix cannot hide malformed UTF-8
later in the scanned suffix; exact first-unit error evidence is retained.

Six new regressions compare finite word languages against an independent prefix
search at every boundary in small Unicode strings, test greedy competition,
multibyte repetition and byte endpoints, empty/no-match distinctions, invalid
positions and malformed suffixes. Functional Syntax token construction,
identification and separator rules are now composed in subsequent components;
full parser composition remains an M3 obligation.


## M3: complete Functional Syntax terminal grammars and selection

Sixteen newly audited public theorems and fifteen independent specification
declarations extend the byte frontend. Ten `Functional` results cover actual
keyword/terminal cloning, keyword/all-terminal compilation, nonempty grammars,
whole-byte recognition and longest-token selection with strict source progress.
Six `FunctionalSelection` results cover the complete terminal enumeration,
actual all-class selector total correctness, exact token availability and bounded
advancing spans. The normal language-tag compiler and a UTF-8 failure exclusion
lemma provide the two remaining composition results.

The 2012 normative inventory contains 71 keywords, four punctuation, seven
variable terminals and two special terminals. An independent checked inventory
connects all keyword spellings and grammar families to both implementations and
full model constructor names. The semantic languages independently characterize
finite keywords, decimal integers, quoted XML text with exactly the two OWL
escapes, the explicitly named RFC 5646 langtag production, SPARQL 2008 names,
absolute IRIs, the four whitespace characters and line-bounded comments.

`next_terminal` visits every family and retains the greatest eligible endpoint.
Its specification is mathematical candidate membership and endpoint maximality,
not a second version of the scan. A valid suffix yields a token exactly when
any family has an eligible candidate. No-match proves absence across every
terminal; malformed suffixes retain exact first UTF-8 failure evidence. Selected
source slices strictly advance within source length.

Eight new regressions exercise complete spelling/case behavior, multiline XML
strings and forbidden foreign escapes, the named language-tag production, IRI
and comment/string context, greedy keyword/name competition, UTF-8 byte offsets,
malformed suffixes and actual all-terminal selection. The executable
`cargo run -p rowl --example functional` prints real maintenance-source spans.

This completes terminal grammars and canonical greatest-endpoint selection.
Pairwise language disjointness is now proved below; separators/trivia are composed
in the whole-source lexer below. Other decoded
payload construction, full document parsing, imported scopes/provenance and
OWL validation/reasoning remain pending under the original full-release gates.


## M3: complete quoted-string payload reading and grammar equivalence

Ten public theorems and fourteen independent declarations connect the actual
reader with complete Functional Syntax quoted-string payload semantics. The
reader reuses the previously verified strict required/expected unit readers and
bounded canonical-unit append; their crate visibility changes add no algorithm
changes. Raw items require XML characters excluding quote/backslash; escapes
accept exactly those two markers. Multiline text remains legal.

Total correctness covers the opening delimiter, strict advancing body scan,
exact decoded byte concatenation, closing quote and output budget. Independent
error relations describe malformed/truncated units, wrong opening/raw XML
characters, foreign escapes and original-source budget failures. Every earlier
item is grammar-legal and fits before a later failure. A partial append is not
returned as a decoded value; the encoder's invalid-scalar branch is excluded.

Acceptance is exactly the independent decoded-token grammar plus output length.
Successful payloads supply source segments in the existing complete terminal
language, and the converse is also proved by decomposing independent grammar
words into strict source units. Every terminal candidate has a decoded payload;
if its byte length fits, the actual reader returns that payload and exact source
end. This bridge composes grammar recognition with decoding without trusting
caller-provided token metadata or adding unproved semantic assumptions.

Five regressions compare all small XML words with an independent spelling oracle,
check decoded values against actual terminal selection, distinguish foreign
N-Triples escapes, exercise all output-byte budgets and original slash offsets,
probe raw XML boundaries and retain Unicode/multiline content. A token reader
may stop before a malformed later suffix; a paired test verifies the separate
selector rejects that same suffix. The Functional Syntax example now actually
unescapes a maintenance label and reports a short-budget failure.

Stream separator/trivia rules are now composed below. Other payload kinds, complete document
parsing, imports/scopes/provenance, M4 composition and OWL reasoning retain their
original release gates. This completes one payload reader, not the full parser.


## M3: whole-source Functional Syntax token streams

`FunctionalSelection.Correct` now specifies the earliest eligible inventory
member at the greatest endpoint. `selected_token_unique` proves exact kind and
both boundaries are unique under that predicate; `next_terminal_token_iff`
connects it in both directions to actual selection. This establishes exact deterministic selection; the additional complete
language-disjointness proof is now checked in the next component.

Eleven audited `FunctionalLexer` theorems cover the seven-codepoint delimiter
predicate, special kinds, final Unicode source codepoints, actual separator
checking with complete endpoint/missing acceptance, bounded separator progress,
whole-source totality, complete token-stream acceptance, unreachable invalid
spans and emitted-stream properties. Independent canonical UTF-8 spans and
terminal languages define token eligibility; mathematical greatest endpoints
and first inventory membership define each selection. Source-linked endings,
EOF/delimiter conditions and maximal trivia endpoints define separators.
Whole-stream derivations define exact source order, token-count precedence
and the first diagnostic after accepted predecessors. The actual recursive
loop is proved to terminate because both trivia and regular steps strictly
advance within the immutable bytes. Budget subtraction is proved safe.

The public operation first checks the full XML-character text. Invalid text is
diagnosed before any token-limit result, even if the error follows otherwise
valid earlier tokens. Special tokens are discarded without consuming emitted
token budgets. Later lexical/separator/budget errors never return successful
partial streams. Every emitted token is nonempty, bounded, ordered, nontrivia
and in its independent source language; emitted counts fit the caller budget.
No parser-assigned or caller-trusted token metadata is assumed.

Seven regression tests exercise the standard spaced/dense literal examples,
keyword/name competition, every regular terminal family, a nested maintenance
ontology with chains and cardinalities, source slices, comments and multiline
hash-containing strings, all budget prefixes, malformed suffixes and Unicode
final codepoints. The Functional Syntax example now runs a complete maintenance
rule through `lex` and demonstrates whole-stream rejection after a later failure.

The section 2.2 step-6 special-token prose ambiguity is explicitly recorded in
architecture.md. Separator checks apply after regular tokens, with discarded
special tokens restarting matching, consistently with the normative document's
examples. Pairwise terminal-language disjointness is now proved below. Nonquoted payload construction,
full OWL document grammar/AST construction, import scope/provenance assembly,
other serializations and complete M3/M4 composition remain pending. Lexical
acceptance does not establish balanced syntax, valid declarations/DL restrictions
or an OWL inference result. Physical resource/cancellation outcomes remain M8.


## M3: complete terminal disjointness and standard greatest-token selection

Six additional audited theorems cover independent keyword-spelling injectivity,
complete terminal-language disjointness, exact byte-candidate kind uniqueness,
equivalence of the priority-free greatest predicate with the prior selector
contract, complete token uniqueness and both directions of actual standard
selection. The new audited `Greatest` specification has no inventory-order
premise and retains original source offsets and mathematical maximality.

The word proof covers all 71 keywords and every punctuation, variable and
special terminal family. A private proof-only classification distinguishes
initial markers/digits/whitespace and colon-sensitive name forms. Every
character/property premise is derived from the independent languages; Unicode
intervals are not replaced by ASCII approximations. Prefix names end in colon;
nonempty local names contain no colon under the referenced SPARQL 2008 grammar.
Equal canonical UTF-8 byte spans have equal codepoint words, completing the
source-byte no-ties theorem. The actual inventory-priority implementation cannot
change any grammar-valid result because only one kind can occupy an endpoint.

Three additional regressions check unique whole-kind recognition for all 84
standard terminal fixtures, Unicode names and keyword/name competition, and
at-most-one kind at every UTF-8 endpoint in representative source snippets.
These tests complement the arbitrary-word proof; they are not its scope limit.
Full Functional Syntax document grammar/AST construction, other payloads,
canonical imported scopes/provenance, other RDF formats and complete M3/M4
composition retain their original release gates. The recorded step-6 prose
interpretation is separate from the mechanically checked no-ties result.

## M3: exact integer payloads from canonical source spans

The actual kernel decimal reader now gives exact nonnegative values from a
nonempty original byte span. Eight newly audited Decimal theorems prove finite
byte-to-Natural construction, multiplication by ten through actual additions,
bounded source scanning, whole/span total correctness, acceptance in both
directions and exact empty/range/first-invalid-digit diagnostics. Leading zeroes
are accepted and no native integer value cap is imposed. An invalid later digit
cannot expose a successful partial value.

Six further FunctionalIntegers theorems connect this reader to the independent
complete Functional Syntax integer language. All canonical ASCII spans equal
their original byte values; integer grammar words are exactly nonempty ASCII
digit words, and canonical source candidates coincide with bounded digit spans.
Actual value acceptance equals the positional value of that source word in
both directions. Actual greatest-selected integers and all integers in a
successfully lexed whole-source stream supply exact values without trusting
caller-supplied token kinds/endpoints. Eight Decimal definitions and the
WordValue/IntegerValues specifications are audited with these proofs.

Six kernel regressions cover every byte, independent small positional-value
oracles, leading zeroes, original nonzero source offsets, empty/reversed/outside
spans, non-ASCII/sign/whitespace rejection and first later errors. Three library
regressions exercise actual greatest selection and complete lexing in all six
object/data cardinality contexts, including Unicode source prefixes and later
whole-source failures. These are lexical/value checks, not complete expression
or ontology acceptance. The Functional Syntax example displays source `003`
as exact value 3.

The original full release requirements remain intact. Other payloads, document
AST construction, import scopes/provenance, remaining RDF formats, concrete
datatype reasoning, complete M3/M4 composition and full SROIQ reasoning remain
pending. Unary arithmetic is a correctness-first research representation;
efficient arithmetic, physical stack/memory and cancellation remain M8 work.

## M3: canonical source copying and complete nonquoted name values

Four SourceSpans theorems prove canonical unit rebasing, both directions of
source-segment/copied-byte UTF-8 equivalence, minimum byte width per scalar and
canonical splitting of concatenated source words. The mathematical Bytes
specification retains the exact original span without normalization.

Eight FunctionalNames theorems prove the value grammar after marker removal,
actual byte-to-value total correctness, exact success/acceptance in both
directions, successful value grammars, all rejection phases in both directions,
actual greatest-selected name values and all names in a complete accepted lexer
stream. The nine name specifications and the source Bytes specification are
audited. Full IRI angle markers, node `_:` and language `@` are removed; prefix
and abbreviated names retain their exact colon-bearing spelling. The payload
budget excludes only removed markers. Full IRIs are absolute and follow the
proved RFC grammar; labels/names follow SPARQL 2008 and Functional language tags
use its explicitly referenced RFC 5646 langtag production.

Invalid span errors precede indexing, invalid-token errors identify the entire
original span start, and budget errors identify the original payload start.
This reader does not claim finer first-character grammar diagnostics. It
revalidates caller spans itself; the selected-token/stream theorems derive kind,
bounds and grammar facts from actual lexing. Malformed outside bytes are a
separate whole-source lexer obligation. A raw-copy budget-error fallback is
proved unreachable after the public range guards.

Six frontend and two library regressions check all five value families,
Unicode/percent/case preservation, original nonzero offsets, marker-excluding
budget boundaries, invalid ranges and empty words, wrong families and foreign
escape dialects, split/malformed UTF-8 and later whole-source failures. A complete
maintenance token stream exercises every family, and the example displays an
actual full IRI payload. These remain lexical/value examples, not AST validation
or inference. Distinct NameKind/NameError types resolve a generated-instance name
collision with the kernel; no extraction assumption or generated-code rewrite
is introduced.

At this name-reader stage the existing prefix-parts expansion API stays separate.
Source-derived abbreviation splitting and resolution are completed in the next
block below. Leading prefix parsing is completed in the final block below;
remaining ontology header/body parsing, role/scoped identity construction,
literal/document AST construction, imports/provenance and complete M3/M4
composition remain pending. All original format, datatype,
SROIQ, query and byte-to-answer release requirements remain intact.


## M3: source-derived abbreviation parts and complete IRI resolution

Seven FunctionalIriParts theorems establish exact prefix/local grammar and byte
restoration, actual splitting total correctness, complete acceptance, source
value preservation, unique independent partitions, every source error phase in
both directions and exact successful parts in both directions. Four independent
specifications describe canonical source partitions, source parts and error/result
contracts. The actual scan decodes scalars and finds the syntax colon; absence of
colon in permitted prefix bodies is derived from the normative Unicode grammar.
Internal fallback errors are proved unreachable for every public input.

Six FunctionalIris theorems compose source-derived parts with the immutable
prefix table and establish actual resolution total correctness, exact successful
values in both directions, complete independent admissibility, all errors in both
directions, final absolute-IRI grammar and unreachable internal parts errors.
Four independent specifications describe exact success, diagnostics, total results
and mathematical admissibility. Source errors precede lookup; missing names precede
final limits; limits precede final IRI validation. All four standard namespaces,
case-sensitive labels and unmodified Unicode/percent spellings are preserved.
Budgets count final IRI bytes, independently of a longer source prefix. Full-IRI
limit errors identify the original payload start; expansion failures identify the
original complete abbreviation start.

Eight frontend regressions cover standard/default/Unicode/case-distinct names,
source-derived separators at nonzero original offsets, shorter final budgets,
wrong families, invalid ranges and malformed UTF-8, diagnostic priority and a
SPARQL-valid supplementary noncharacter rejected by final RFC IRI validation.
One library regression resolves every IRI in a complete maintenance token stream
and checks that a later source failure rejects the stream. A separate runnable
example shows `ex:Pump` becoming the maintenance namespace IRI and the original
missing-prefix diagnostic. This resolver API receives a checked declaration table;
the next block derives its records from the original bytes. These
examples perform IRI value resolution, not OWL document parsing or inference.

The original complete release scope remains unchanged. Leading prefix/ontology
opening parsing is proved below. Remaining header/body grammar, canonical identities,
literals/document AST construction, byte-derived
import metadata/provenance, remaining serializations, full M3/M4 composition,
concrete datatype reasoning, all SROIQ/query proofs and operational M8 outcomes
remain pending. M3 and M4 are still in progress and full release remains disabled.

## M3: source prefix declarations and checked IRI composition

The actual `functional_prefixes::read_prefix_header` now reads all leading
Functional Syntax Prefix declarations and the exact Ontology opening from the
original source bytes. It runs complete lexing first, preserving the priority of
later UTF-8/XML/terminal/separator errors over all prefix-stage errors. The
result retains exact source declaration order and spelling, both original
opening tokens and the untouched remainder. This is deliberately a partial
parser stage: `Ontology(` can be accepted here while full document parsing must
still reject the missing body/closing punctuation.

Five `FunctionalPrefixShape` theorems and six independent specifications prove
the expected-terminal discriminator, total single-token consumption, total
complete body skeleton reading, exact result/error equivalence and five-token
consumption. EOF mismatches retain the original source length, including later
discarded trivia; wrong terminal errors retain the actual original token start.
Five `FunctionalPrefixDeclaration` theorems and one independent BodyRun
specification compose exact source payloads, value grammars, per-field budgets,
all result/error phases and strict token progress. Full declaration syntax is
checked before the prefix value, then the namespace value.

Eight `FunctionalPrefixes` theorems and three independent run/result/section
specifications prove total repeated scanning, exact result equivalence, total
public byte reading, complete successful acceptance, every syntax/count/value
error in both directions, exact source rows/count/grammars, checked-source table
preservation and unreachable InvalidSpan. Each Prefix keyword checks the
declaration-count limit before its body. Lexical errors retain the existing
lexer contract; the syntax-error equivalence starts only after complete lexing.
The successful source theorem establishes the complete leading-prefix
derivation ending at the exact original ontology opening.

Raw syntax reading deliberately retains duplicate and reserved declarations.
The normative `prefixes::check` constructor must still reject these before use,
even when their names never occur in the body. Its checked-source composition
retains precisely the original parsed declaration vector. Three further
`FunctionalPrefixResolution` theorems compose source parsing, table checking and
actual full/abbreviated IRI resolution with final IRI validity and exact successful
value/error equivalences on the source-derived declaration rows.

Eight frontend and two library regressions cover Unicode/default/case-distinct
declarations, composed versus decomposed spelling, original opening offsets and
unchanged suffixes, every missing/wrong body terminal, EOF/trivia offsets, raw
duplicate/reserved rows, independent count/value/token limits and phase priority,
later whole-source lexical failures and intentional partial-stage acceptance.
The runnable `functional_prefixes` example derives its maintenance namespace from
source bytes, checks the table and resolves all source IRIs, including `ex:Pump`
and `ex:pump7`. It does not construct a complete ontology or perform inference.

This block adds 21 audited public theorems and ten independent definitions:
507 theorems, 455 definitions, 280 Rust tests and 700 ledger obligations overall.
M3/M4 remain in progress. Ontology/version IRIs and leading imports are proved
in the next block. Annotations, axioms, scopes and complete byte-to-AST assembly,
all other original format,
datatype, SROIQ/query and operational release requirements remain pending.

## M3: source ontology identity/version and leading imports

The actual `functional_header::read_header_tail` now reads the standard optional
ontology/version identity and the maximal leading import sequence from the
unchanged tokens after the original Ontology opening. Full and abbreviated IRIs
are resolved from their actual source spans with the same normative checked
prefix table. Original IRI tokens, keyword tokens, reference order/repetitions and
the first non-Import/empty suffix are retained. SourceOntologyIdentity represents
anonymous, named without version and named with version; a version never occurs
without its ontology IRI. It has a distinct frontend name to avoid a pinned
extractor derived-instance collision with the kernel's OntologyIdentity.

Nine FunctionalHeaderIdentity theorems and five independent definitions prove
terminal classification, total optional and identity reading, exact value/error
equivalence, unchanged absence, exact present-token/source values, all identity
source values and complete absolute-IRI grammar. Six FunctionalHeaderShape
theorems and six independent specifications prove terminal alternatives, total
single-token/skeleton reading, exact skeleton value/error equivalence and exact
three-token consumption. Four FunctionalHeaderImport theorems and one independent
BodyRun relation compose syntax with exact target resolution, complete value/error
equivalence, source token/value preservation and strict token progress.

Six FunctionalHeader theorems and three independent run/section relations prove
total repeated scanning, exact results/errors in both directions, total complete
identity-then-import reading, exact header result equivalence, maximal stopping,
original identity/reference source values and bounded reference counts. Every
Import keyword checks the count limit before its body; complete body syntax
precedes IRI resolution. Accepted imports consume four tokens with their keyword.
EOF mismatches retain the complete original byte length including discarded
trivia, and other syntax/IRI failures retain established original offsets.

Two FunctionalHeaderSource composition theorems connect actual original-byte
prefix lexing/parsing and successful normative table checking to the header
reader's exact result/error contract and all source identity/import values.
No namespace metadata is supplied independently in this pipeline. The low-level
reader itself receives tokens and a checked table; complete source validation
comes from the preceding byte entry point. Ontology annotations, axioms, closing
punctuation and unexpected trailing tokens are deliberately left unchanged.
Accepting this partial header does not establish full document validity or a
canonical import closure. The existing indexed resolver still receives supplied
symbol/dependency metadata; catalog/index composition with these source targets
and complete grammar/AST construction remain pending.

Eight frontend and two library regressions cover all identity forms, anonymous
ontologies with imports, Unicode/case/percent preservation, ordered repeated
references, original keyword/target offsets, every truncated/wrong import stage,
full EOF lengths after comments, separate count/final-value budgets and phase
priority, undeclared ontology/version/import names, arbitrary low-level span
revalidation, intact annotations/axioms/closing/unexpected suffixes and whole-byte
lexical or duplicate-prefix failures before header metadata exposure. The runnable
functional_header example reads plant/v2 identity and maintenance-parts/machines
imports from the same original source; it performs neither catalog closure nor
OWL inference.

This block adds 27 public theorems and 15 independent definitions: totals are
534 audited theorems, 470 definitions, 290 Rust regressions and 727 ledger
obligations. Full M3/M4, remaining formats, canonical scopes/provenance, normative
datatypes, SROIQ/query proofs and byte-to-answer release remain pending.


## M3: exact Functional Syntax literal source reading

`functional_literals::read_literal` borrows an immutable checked prefix table
and original byte buffer, consumes one supplied literal position and returns
its exact lexical/datatype fields, original quote/form tokens and untouched
suffix. The complete original byte lexer runs separately; this reader also
revalidates all supplied quote, language and datatype spans.

The normative [OWL 2 literal rules](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Literals)
require both plain-string shortcuts to expand during parsing. `"Pump"` has
structural lexical bytes `Pump@`, and `"Pump"@de` has `Pump@de`; both have the
exact rdf:PlainLiteral datatype. Language spelling/case and internal '@' bytes
are retained. Explicit `"abc"^^rdf:PlainLiteral` remains lexical `abc`, and
`"001"^^xsd:integer` remains `001`. The reader does not validate concrete datatype
lexical/value spaces: `"+"^^xsd:integer` can be read as a raw literal, and must
be rejected by the later normative datatype validator. RDF 1.1 literals have
separate syntax conventions and their existing raw RDF representation.

The independent shape/error relations prove all written syntax is checked before
payload decoding, exact one/two/three-terminal consumption and strict progress.
Range checks precede quote errors; the quote's returned endpoint must match the
supplied span. Every exact quote/span result and error is equivalent to the source
contract. The quote payload module additionally now proves reverse first-error
acceptance for opening, required units, escaped/raw items and output budgets.
The bounded copy/concatenation primitives have reusable public totality/exactness
proofs. Plain expansion's full output bound includes '@' and every language byte;
constant datatype budget failure follows lexical expansion failure. Typed values
resolve their original IRI with the separate final datatype budget.

FunctionalLiterals composes every phase into totality and exact result/error
iff independent Run derivations. Success theorems establish original tokens,
quote progress, both final budgets and required expansion/exact typed spelling.
FunctionalLiteralSource composes original whole-byte prefix lexing/parsing and
normative table checking using precisely the namespaces from that source. The
caller still supplies the literal position: no annotation/axiom or complete
ontology grammar/AST is claimed, nor canonical catalog/import/scopes/provenance,
concrete normative datatype validity or general OWL reasoning.

Nine frontend and three public-library regressions cover Unicode and multiline
text, quote/backslash unescaping, rejection of foreign escape syntax, empty and
language strings, internal '@', exact tag case, explicit rdf:PlainLiteral and
integer spellings, custom source namespace expansion, malformed supplied spans,
missing/wrong syntax and original full EOF offsets, intact suffixes, final output
limits and phase priority. The maintenance-literals.ofn fixture and runnable
functional_literals example show exact readings from actual source annotations;
the demo's token locator is explicitly separate from full annotation parsing.

This block adds 25 public theorems and 14 independent definitions: totals are
559 audited theorems, 484 definitions, 302 Rust regressions and 752 ledger
obligations. Full M3/M4, all required formats/export laws, normative datatypes,
SROIQ/query and complete byte-to-answer release proofs remain pending.


## M3: Functional Syntax annotations with recursive nesting

`functional_annotations::read_annotations` borrows the checked prefix table and
original byte buffer and reads the maximal leading `{ Annotation }` sequence of a
token stream in source order, such as the ontology annotations after the header.
Each `Annotation( {Annotation} property value )` may carry its own annotations,
read recursively one level deeper. Properties and IRI values resolve their
original full/abbreviated spans through the checked table. Node-ID values keep
their exact label without `_:`. Literal values reuse the proved literal reader,
so the mandatory rdf:PlainLiteral expansion also applies inside annotations.
Records retain the original keyword, property and value tokens, their order and
repetitions. The first non-`Annotation` token and its suffix remain unchanged for
the axiom stage.

Two caller limits bound the recursion. `depth` is the remaining nesting allowance:
0 permits no annotation, and 1 permits only unannotated annotations. `count` bounds
each sequence separately, nested or not. `iri` bounds every final IRI, node label
and literal datatype; `lexical` bounds final literal lexical forms. Errors report
the first failing phase in source order: nesting depth, sequence count, `(`, the
nested sequence, property, value, then `)`. EOF errors use the source length.
No partial sequence is returned after an error.

FunctionalAnnotationParts proves the one-token syntax step, the property and
value readers and the property-value-close tail total, with exact result/error
equivalence to the independent TakeRun, PropertyRun, ValueRun and FinishRun
derivations. Their fallback branches after a checked token cannot occur.
FunctionalAnnotations defines the recursive ScanRun grammar and proves the actual
scanner total by well-founded recursion on the token count: the nested call starts
after `Annotation(`, and the continuing call starts after the complete annotation.
Every exact result and first error is equivalent to ScanRun. Success is also
equivalent to the independent maximal Section grammar with per-sequence count
bounds. The returned suffix is empty or starts with a non-`Annotation` token,
top-level records keep their keyword and exact property IRI, and each top-level
annotation consumes at least five tokens. FunctionalAnnotationSource composes
original whole-byte prefix parsing, normative table checking and header reading
with the ontology-annotation contract on precisely those source namespace rows.

This stage assigns no anonymous-individual scopes and constructs no kernel
`Annotation` values. Axioms, the ontology closing token, complete document/AST
construction, canonical imports/provenance and concrete datatype validity remain
pending. Annotation recursion uses the physical stack: the depth limit bounds it,
while typed memory/stack/cancellation outcomes remain M8 work.

Ten frontend and two public-library regressions cover all three value families,
exact tokens and source order, three-level nesting, depth and per-sequence count
limits with their original offsets, every missing or wrong terminal with its EOF
or token offset, property/value/label/literal budget and resolution failures,
nested-first priority, absent annotations, preserved suffixes and multibyte
Unicode offsets. The maintenance-annotations.ofn fixture and the runnable
functional_annotations example print the nested ontology annotations of a source
document and the depth-limit diagnostic.

This block adds 27 public theorems and 8 independent definitions: totals are
586 audited theorems, 492 definitions, 314 Rust regressions and 779 ledger
obligations. Full M3/M4, all required formats/export laws, normative datatypes,
SROIQ/query and complete byte-to-answer release proofs remain pending.


## M3: Functional Syntax entity declarations

`functional_declarations::read_declaration` borrows the checked prefix table and
original byte buffer and reads exactly one `Declaration( {Annotation} Entity )`
axiom at a caller-supplied position. The entity is `Class`, `Datatype`,
`ObjectProperty`, `DataProperty`, `AnnotationProperty` or `NamedIndividual`
applied to one full or abbreviated IRI. The axiom annotations reuse the proved
annotation reader with the caller's `AnnotationLimits`; the entity IRI resolves
its original span through the checked table under the same `iri` limit. The
record keeps the original `Declaration` and entity keyword tokens, the IRI token
and its exact value; the suffix after the closing parenthesis stays unchanged.

Errors report the first failing step in source order: the `Declaration` keyword,
`(`, the axiom annotations, the entity keyword, its `(`, the IRI token, the IRI
resolution, then both `)` tokens. EOF errors use the source length. As in the
annotation stage, the IRI is resolved before the closing tokens are checked.

FunctionalDeclarations proves entity-keyword classification and the one-token
syntax step exact, and the actual entity and declaration readers total, with
exact result/error equivalence to the independent EntityRun and DeclarationRun
derivations. The declaration grammar uses the independent annotation ScanRun for
its axiom annotations. The fallbacks after a checked entity keyword or IRI token
cannot occur. Success gives the keyword's exact entity kind, a source-linked IRI
value, axiom annotations equal to the independent maximal annotation Section, and
at least seven consumed tokens plus five per top-level annotation, the progress
fact a later axiom loop needs. FunctionalDeclarationSource composes original
whole-byte prefix parsing and normative table checking with the declaration
contract. The new public FunctionalAnnotations.scan_section_accepted lemma turns
any successful top-level annotation derivation into its Section.

The reader constructs source records only. Declaration typing, punning and the
reserved vocabulary stay the existing separate kernel checks; for example,
`Declaration(ObjectProperty(owl:Thing))` is read here, and the reserved-vocabulary
check rejects it once declarations reach the kernel model. That mapping, the axiom
loop, the other axiom forms, the ontology
closing token, complete document/AST construction, canonical imports/provenance
and kernel Declaration values remain pending.

Six frontend and two public-library regressions cover all six entity kinds with
exact tokens and IRIs, nested and anonymous-valued axiom annotations with their
depth and count limits, every missing or wrong terminal with its EOF or token
offset, IRI resolution and budget failures, source-order priority, reserved and
punned names left to later checks, and multibyte Unicode offsets. The
maintenance-declarations.ofn fixture and the runnable functional_declarations
example read all seven declarations of a source document, including one with an
axiom annotation, and stop at the ontology's closing token.

This block adds 14 public theorems and 5 independent definitions: totals are
600 audited theorems, 497 definitions, 322 Rust regressions and 793 ledger
obligations. Full M3/M4, all required formats/export laws, normative datatypes,
SROIQ/query and complete byte-to-answer release proofs remain pending.


## M3: Functional Syntax annotation axioms

`functional_annotation_axioms::read_annotation_axiom` reads exactly one
annotation axiom at a caller-supplied position:
`AnnotationAssertion( {Annotation} property subject value )`,
`SubAnnotationPropertyOf( {Annotation} sub super )`,
`AnnotationPropertyDomain( {Annotation} property IRI )` or
`AnnotationPropertyRange( {Annotation} property IRI )`. Axiom annotations reuse
the proved annotation reader and assertion values reuse its value reader, so
literal values keep the mandatory rdf:PlainLiteral expansion. Every property,
subject and domain/range IRI resolves its original span through the checked prefix
table under the `iri` limit. A node-ID subject keeps its exact label without `_:`;
its scope belongs to the later import assembler. Records keep the original keyword
and IRI tokens, and the suffix after the closing parenthesis stays unchanged.

Errors report the first failing step in source order: the axiom keyword, `(`, the
axiom annotations, the body positions, then `)`. EOF errors use the source length.
A wrong assertion value is reported by the shared value reader inside a `Value`
error, so its diagnostics stay identical to those of annotation values.

FunctionalAnnotationAxioms proves keyword and subject classification and the
one-token syntax step exact, and the actual IRI, subject, body and axiom readers
total, with exact result/error equivalence to the independent IriRun, SubjectRun,
BodyRun and AxiomRun derivations. The IRI reader is proved at both IRI positions,
and the fallbacks after a checked keyword, IRI or subject token cannot occur.
Success gives a body whose kind matches the keyword, axiom annotations equal to
the independent maximal annotation Section, and at least five consumed tokens
plus five per top-level annotation. FunctionalAnnotationAxiomSource composes
original whole-byte prefix parsing and normative table checking with the
annotation-axiom contract.

With declarations, every non-logical axiom form now has a proved reader. The
logical axioms (classes, properties, individuals, keys and datatype definitions),
the axiom loop, the ontology closing token, complete document/AST construction,
anonymous scopes and kernel axiom values remain pending.

Four frontend and two public-library regressions cover all four forms with exact
IRIs and both subject families, IRI and node-ID values, axiom annotations with
their depth limit, every missing or wrong terminal with its EOF or token offset,
the shared value diagnostic, and property, subject, label, literal-datatype and
domain resolution failures. The maintenance-vocabulary.ofn fixture and the
runnable functional_annotation_axioms example read a vocabulary ontology of
declarations and annotation axioms up to its closing token.

This block adds 20 public theorems and 9 independent definitions: totals are
620 audited theorems, 506 definitions, 328 Rust regressions and 813 ledger
obligations. Full M3/M4, all required formats/export laws, normative datatypes,
SROIQ/query and complete byte-to-answer release proofs remain pending.


## Reasoner track: negation normal form for the ALC fragment

`nnf::nnf` translates an OWL class expression (positive polarity) or its
complement (negative polarity) into `NnfConcept`, the input language of the
coming tableau. The concept type has top, bottom, named classes, negated named
classes, binary conjunction and disjunction, and existential and universal
restrictions on named object properties, so negation can only occur on named
classes. The supported fragment is ALC: named classes, intersections, unions,
complements and existential/universal restrictions on named properties. Every
other form, including inverse properties, enumerations, value and self
restrictions, cardinalities and data restrictions, returns `None`; later
reasoner stages extend the fragment.

De Morgan's laws and quantifier duality move negation inward; double negation
cancels. `owl:Thing` and `owl:Nothing` become top and bottom by exact IRI, using
the existing `is_thing` check and the new matching `is_nothing`. Other class and
property IRIs are copied exactly. Intersection and union members are joined
left-nested in source order, each translated once, so no subexpression is
duplicated.

Nnf proves the translation total on all 18 class forms by well-founded recursion
on expression size, through the mutually recursive member fold and restriction
helpers. It returns a result exactly on the independent InAlc fragment, and the
result means the expression (or its complement) under the independent Direct
Semantics in every interpretation that fixes owl:Thing and owl:Nothing. Every OWL
interpretation does so (fixes_of_interpretation), and the statement holds for
object and data domains of any universe, as the later completeness proof needs.
Consequently a translated concept has instances exactly when the class
expression does (nnf_instances), which reduces OWL class satisfiability in this
fragment to concept satisfiability.

Six kernel regressions check exact output shapes, left-nested member order,
top/bottom handling and near-miss built-in spellings, exact IRI copies,
rejection of every unsupported form even when nested, and a brute-force semantic
comparison: ten expressions in both polarities on all 256 interpretations over a
two-element domain, against an independently written evaluator. The runnable nnf
example prints the normal form of maintenance expressions.

This block adds 7 public theorems and 11 independent definitions: totals are
627 audited theorems, 517 definitions, 334 Rust regressions and 820 ledger
obligations. The tableau, TBox reasoning and blocking, the remaining
constructors, normative datatypes, query reductions and full OWL decisions remain
pending.
