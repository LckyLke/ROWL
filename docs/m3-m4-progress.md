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


## Reasoner track: verified ALC tableau without a TBox

`tableau::satisfiable` decides whether some interpretation has an element in a
negation-normal-form concept. `expand` works on two lists: pending concepts and
literals (named classes, negated named classes and restrictions). It drops top,
rejects bottom, splits a conjunction into both operands and tries each operand of
a disjunction. Every other concept moves to the literals. When nothing is
pending, a named class that occurs both positively and negated is a clash.
Otherwise every existential restriction `∃r.C` is decided recursively as the
list `C` plus the filler of every universal restriction `∀r.D` on the same
property. Classes and properties are compared by exact IRI spelling. Following
the kernel's extraction subset, lists are borrowed cons lists passed by value and
handed back, and branching uses an explicit `duplicate`.

Tableau proves every helper exact: duplication, positive-atom search, clash
detection and universal-filler collection. The main theorem proves `expand`
total by well-founded recursion on the lexicographic pair (total concept size,
pending concept size): expansions and disjunctions shrink the total, moving a
literal shrinks the pending size, and each successor list is smaller than the
literals that produced it. Soundness builds an explicit tree interpretation over
paths: the root carries the positive named classes, and the i-th existential
leads to the root of the i-th successor's tree model, chosen classically. The
subtree lemma shows that the tree agrees with each successor model below the
root. Completeness follows any model, in any universe: a model has no clash,
satisfies one operand of every disjunction, and supplies a successor for every
existential that satisfies all the matching universal fillers.

Composed with the NNF stage, the tableau never rejects an OWL class expression
that has an instance in an OWL interpretation (class_instances_accepted), so a
rejection proves the expression empty in every OWL interpretation
(rejected_class_empty). This justifies unsatisfiability and subsumption answers
for ALC. Acceptance yields a tree model of the concept; turning it into an OWL
model that also fixes owl:Thing and owl:Nothing, TBox axioms with blocking, the
remaining SROIQ constructors, datatypes, ontology-level queries and performance
remain pending. This is an internal fragment experiment toward M6.

Five kernel regressions check propositional clashes and branching, successors
for existentials only, propagation through nested restrictions, OWL subsumption
through negation normal form, and that every one of 2000 pseudo-random concepts
with a model of at most three elements is accepted. The runnable tableau example
answers maintenance satisfiability and subsumption questions.

This block adds 20 public theorems and 14 independent definitions: totals are
647 audited theorems, 531 definitions, 339 Rust regressions and 840 ledger
obligations. Full OWL reasoning, ontology-level queries and byte-to-answer
release proofs remain pending.


## Reasoner track: verified ALC tableau with a TBox and blocking

`tbox::satisfiable_in` decides whether some interpretation in which a TBox
concept holds at every element has an element in a concept; both are in negation
normal form. The TBox is one concept, for example the negation normal form of the
conjunction of `¬C ⊔ D` for general concept inclusions `C ⊑ D`. `expand` keeps
the plain tableau's rules over pending concepts and literals and adds a third
list, the history: the literal sets of the node's ancestors, nearest first. When
nothing is pending and there is no clash, a node whose literals all occur in one
ancestor's literal set is blocked and accepted. Otherwise its literal set joins
the history, and every existential restriction `∃r.C` is decided as the list `C`,
the TBox concept and the fillers of the universal restrictions `∀r.D` on the same
property, below the extended history. Concepts are compared structurally, with
classes and properties compared by exact IRI spelling.

Hintikka, which is independent of the Rust code, defines syntactic satisfaction
of a concept by a literal set, clash-freedom, witnessed existentials and coherent
families. Every set of a coherent family is clash-free, satisfies the TBox
concept, and has each existential restriction witnessed by a set in the family
(or among given ancestors) that satisfies the TBox concept, the filler and every
matching universal filler. Its truth lemma takes the interpretation whose
elements are the sets of a coherent family, with an edge from one set to another
along a property when the second satisfies every universal filler of the first on
that property, and proves every concept true wherever it is syntactically
satisfied. A coherent family with a set satisfying a concept therefore yields a
model of the TBox concept with an instance of the concept.

TboxTableau proves every helper exact: history duplication, structural concept
equality, membership, subset and blocking. The main theorem proves `expand` total
and correct under invariants: all concepts stay inside the subconcept closure of
the input and TBox concepts, the ancestors' literal sets are pairwise distinct,
the literal list holds only literals, and satisfying the current concepts entails
the node's goals, which include the TBox concept. Termination is well-founded on
the lexicographic triple (2^|closure| - |history|, total concept size, pending
concept size). A counting lemma bounds pairwise distinct subsets of the closure by
2^|closure|, and an unblocked node's literal set differs from every ancestor's,
so each successor call shrinks the first component. Soundness is relative to the
ancestors: an acceptance yields a family, coherent with respect to the ancestors,
in which some set or some ancestor satisfies all current concepts. A blocked node
is covered by the ancestor containing its literals; an expanded node adds its own
literal set to the merged families of its successors. At the root there are no
ancestors, so the family is coherent and yields the model. Completeness follows
any model, in any universe, in which the TBox concept holds everywhere. Such a
model has no clash, satisfies one operand of every disjunction, and supplies for
every existential a successor that satisfies the TBox concept and all matching
universal fillers; blocking only ever accepts.

satisfiable_in_correct states the result. Every acceptance comes with a model in
which the TBox concept holds at every element and the concept has an instance,
and every such model, in any universe, forces acceptance. A rejection therefore
proves the concept empty in all of them (rejected_empty_in_models). Composed with
the NNF stage, the procedure never rejects an OWL class expression with an
instance in an OWL interpretation where the TBox class expression holds at every
element (class_instances_accepted_in). So a rejection proves the expression
empty in all such interpretations (rejected_class_empty_in), which justifies
unsatisfiability and subsumption answers under ALC general concept inclusions
expressed as that class expression. Reading SubClassOf and the other class axioms
of an ontology into it, the OWL-level model fixing owl:Thing and owl:Nothing, the
remaining SROIQ constructors and role axioms, datatypes, ontology-level queries
and performance remain pending. This is an internal fragment experiment toward
M6.

Four kernel regressions check that cyclic axioms terminate through blocking, that
axioms propagate to every element (including a clashing cycle and a universal
axiom acting as a range), and that a top TBox agrees with the plain tableau on
1000 pseudo-random concepts. The fourth draws 600 pseudo-random concept and TBox
pairs and checks that every pair with a model of at most three elements is
accepted. The runnable tbox example answers maintenance questions under four
axioms, one of them cyclic.

This block adds 18 public theorems and 13 independent definitions: totals are
665 audited theorems, 544 definitions, 343 Rust regressions and 858 ledger
obligations. Full OWL reasoning, ontology-level queries and byte-to-answer
release proofs remain pending.


## Reasoner track: verified ontology-level ALC queries

`alc_ontology::internalize` turns an axiom closure into one TBox concept in
negation normal form. Each supported axiom contributes a concept that holds at
every element exactly when the axiom holds:

- `SubClassOf(C D)` contributes `¬C ⊔ D`.
- `EquivalentClasses` contributes "all members, or none of them".
- `DisjointClasses` contributes, for every two member occurrences, "not both".
  Occurrences are compared, not expressions, so a repeated member must be empty.
- `DisjointUnion(A ...)` also equates `A` with the union of its members.
- `ObjectPropertyDomain(P C)` contributes `∀P.⊥ ⊔ C`, and
  `ObjectPropertyRange(P C)` contributes `∀P.C`, on a named property `P`.
- Declarations and the four annotation axioms contribute top.

Every class expression goes through the proved NNF translation (the member
joins reuse its `connect`). Any other axiom, an inverse property or an
expression outside ALC gives no TBox concept.

The queries are `consistent`, `class_satisfiable` and `subsumed`. Subsumption
tests the intersection of `sub` with the complement of `sup`. Each query
translates its expressions and then checks that no translated concept uses
owl:topObjectProperty or owl:bottomObjectProperty as a role, or owl:Thing or
owl:Nothing as an ordinary named class. The translation already turns those two
classes into top and bottom. The tableau treats every role as an ordinary one,
but OWL fixes the meaning of the two built-in properties. When the check passes,
the query runs the tableau with blocking against the TBox concept.

Internalization proves `axiom_concept` and `internalize` exact against the
independent Direct Semantics. The result is defined exactly when every axiom is
supported. Its concept holds at every element exactly when an interpretation
fixing owl:Thing and owl:Nothing satisfies the axiom, or the whole closure. Two
semantic lemmas read the axiom conditions one element at a time.
Equivalent-class equality of denotations becomes "all or none" at each element.
Pairwise disjointness of denotations becomes pairwise exclusion at each element.
The pairwise construction is proved by well-founded recursion over member
indices, with its exact support condition.

AlcOntology proves the built-in name checks exact, using byte comparisons
against the fixed OWL spellings. It also proves reinterpreting anonymous
individuals irrelevant to every concept. It then builds an OWL interpretation
from any tableau model:

- Objects and data values are lifted into the requested universes.
- owl:Thing, owl:Nothing and the top and bottom object and data properties get
  their fixed meaning.
- Every other class and object property keeps the tableau's reading.
- Data values are the datatype map's values, embedded through `Option`.
- Datatypes, literals and facets are read from the datatype map.

owl_model_valid proves that this is an OWL interpretation in the sense of
IsInterpretation. owl_model_agrees proves that it gives every proper concept
its tableau meaning.

consistent_correct, class_satisfiable_correct and subsumed_correct state the
results. Each query answers exactly when the closure is supported and the
translations are proper. Then, for every valid vocabulary, its answer equals
Consistent, ClassSatisfiable or Subsumed of the independent semantics, for any
object universe and any data universe that holds the datatype map's values. An
acceptance yields the constructed OWL model of the closure. Any OWL model, in
any universe, forces acceptance through the tableau's completeness, because
every model fixes the built-in classes and satisfies the internalized concept.
consistent_complete, class_satisfiable_complete and subsumed_sound state this
direction for all universes and every vocabulary, valid or not: a model forces
a positive consistency or satisfiability answer, and a positive subsumption
answer holds in every model.

Six kernel regressions cover:

- subclass chains with disjointness, and built-in class bounds;
- equivalence and disjoint unions, including a repeated disjoint member;
- consistency checks;
- domain and range axioms;
- unsupported inputs: assertions, inverse properties and the universal object
  property;
- two randomized checks against all interpretations with at most three
  elements. One checks that the internalized concept holds everywhere exactly
  when the axioms hold. The other checks that every class with a small model of
  its axioms is satisfiable.

The runnable alc_ontology example answers consistency, subsumption and
satisfiability questions for an eight-axiom maintenance ontology. It also shows
that an added class assertion is outside the fragment.

Individuals and assertions, the other axiom forms, the remaining SROIQ
constructors and role axioms, datatypes, the frontend's reading of logical
axioms, query answering and performance remain pending. This is an internal
fragment experiment toward M6.

This block adds 18 public theorems (17 new, and the NNF member-join lemma made
public) and 4 independent definitions. Totals are 683 audited theorems, 548
definitions, 349 Rust regressions and 876 ledger obligations. Full OWL
reasoning and byte-to-answer release proofs remain pending.


## M3: Functional Syntax class expressions and class axioms

`functional_classes::read_class_expression` reads one class expression at a
caller-supplied position:

- a named class IRI;
- `ObjectIntersectionOf` and `ObjectUnionOf` with at least two members;
- `ObjectComplementOf`;
- `ObjectSomeValuesFrom` and `ObjectAllValuesFrom` over an object property
  expression. That expression is an IRI or `ObjectInverseOf( IRI )`, read by
  `read_object_property`.

The other twelve class-expression forms are reported as `Unsupported` at their
keyword. Every IRI resolves its original span through the checked prefix table
under the `iri` limit. Records keep the original keyword and IRI tokens.

Errors report the first failing step in source order with original offsets, and
EOF errors use the source length. At a connective keyword the order is:

1. the nesting depth;
2. `(`;
3. the operands in order, each member of an intersection or union after the
   member-count check;
4. the two-member minimum;
5. `)`.

The reader is three mutually recursive functions: `read_class`,
`read_connective` and `read_members`. FunctionalClasses gives the independent
grammar as three mutually inductive derivations (ClassRun, ConnectiveRun and
MembersRun), with PropertyRun and ResolveRun for the non-recursive parts. The
totality theorems prove the reader terminates on every token stream by
well-founded recursion on (token count, rank). They also prove progress: an
accepted expression consumes at least one token. The execution theorems prove
the converse with the same measure: every derivation is the actual result. The
`_result_iff` theorems combine both directions.

`functional_class_axioms::read_class_axiom` reads one `SubClassOf`,
`EquivalentClasses`, `DisjointClasses`, `DisjointUnion`,
`ObjectPropertyDomain` or `ObjectPropertyRange` axiom. In source order it reads
the keyword, `(`, the axiom annotations with the proved annotation reader, the
body, then `)`. Bodies read class expressions at the full nesting allowance and
object property expressions with the same readers. Member lists reuse the
member sequence followed by the two-member minimum. The disjoint union's class
IRI resolves through the checked prefix table. FunctionalClassAxioms composes
the proved grammars into AxiomRun and proves totality and exact result/error
equivalence. FunctionalClassSource composes both readers with the namespace
rows parsed from the same original bytes.

The regressions cover:

- nested shapes with exact tokens and IRIs;
- inverse properties;
- every error point in source order, including unsupported forms and
  undeclared prefixes;
- depth and count limits;
- 120 printed pseudo-random expressions that must read back to their shape;
- all six axiom forms and axiom annotations;
- the maintenance class ontology, read axiom by axiom in source order.

The runnable functional_class_axioms example reads that ontology from source
and asks the verified reasoner whether it is consistent and about subsumption
and satisfiability. It now uses the verified end-to-end functions (see "From
source bytes to verified answers" below); its earlier hand-written conversion
into the kernel's model is gone.

The other logical axioms and class-expression forms, data ranges and individuals
remain pending. The axiom loop, the closing token, document construction and the
mapping into the kernel's model are proved in the later stages below.

This block adds 41 public theorems and 17 independent definitions. Totals are
724 audited theorems, 565 definitions, 359 Rust regressions and 917 ledger
obligations. Full M3/M4 parsing and byte-to-answer release proofs remain pending.


## One extraction for frontend and kernel

The frontend stages moved from `rowl-frontend` into `rowl-kernel`, and
`rowl-frontend` now re-exports them under their historical paths. All Rust paths,
tests and examples are unchanged. Document assembly will hand parsed axioms to
the reasoner. With two extractions, the frontend and the kernel would each have
their own generated copy of the shared types, and connecting the copies would
need an unproved assumption. With one extraction (namespace `RowlRust`, file
`RowlKernel.lean`), the frontend's output and the reasoner's input are the same
Lean values.

The generated development has exactly the same 912 definitions as the two
former files combined. The 45 frontend proof modules changed only their
namespace and generated import. Every theorem, specification and ledger
obligation is unchanged; the ledger's Rust symbols now name the defining crate,
`rowl_kernel`.


## M3: Functional Syntax documents

`functional_document::read_document` reads a whole document from its original
bytes. It runs the proved prefix-header reader and the normative table check.
`read_document_tail` then reads everything after `Ontology(` in source order:

1. the ontology identity and imports, with the proved header reader;
2. the maximal ontology-annotation sequence;
3. the axiom loop;
4. `)`;
5. the end of the source.

The loop stops before `)`. Every other token must start one of the 37 axiom
forms:

- declarations, the four annotation axioms and the six class, domain and range
  axioms go to their proved readers with the caller's limits;
- the other logical axioms are reported as `UnsupportedAxiom` at their keyword.

The axiom count is checked before each axiom is read.

FunctionalDocument specifies the loop as AxiomsRun, with one axiom step per
family (AxiomStep), and the tail as TailRun. The loop is proved total by
well-founded recursion on the token count. Every successful axiom consumes at
least one token: declarations and annotation axioms by their existing progress
theorems, and class axioms by the new class_axiom_progress. Execution follows
the grammar by induction on the derivation. The tail's end-of-source fallback
before `)` is proved unreachable, because a successful loop always stops at `)`.
The whole-document theorems:

- prove totality;
- report a prefix failure or a rejected table, by kind, as the first error;
- given the declarations parsed from the same bytes and accepted by the checker,
  equate every result with the independent tail derivation, keeping the
  original declarations.

Three regressions read all five maintenance example documents completely and
check that axioms keep their family and order. They also cover each first error:
an unsupported axiom, a missing `)`, trailing content, a non-axiom token, the
axiom count, a duplicate prefix, a missing ontology and an error inside an axiom.
The functional_class_axioms example now reads its ontology with the verified
document reader.

This block adds 17 public theorems and 6 independent definitions. Totals are
741 audited theorems, 571 definitions, 362 Rust regressions and 934 ledger
obligations. The mapping into the kernel's raw model and end-to-end answers
follow in the next section.


## M3/M6: From source bytes to verified answers

`functional_model::document_ontology` maps a read document into the kernel's raw
OWL ontology:

- the ontology identity, with its version;
- the import targets, in order;
- the ontology annotations, with nested annotations;
- every axiom with its axiom annotations, in source order.

IRI and literal bytes are copied exactly; `copy_bytes` is proved to return its
input. A node ID becomes an anonymous individual whose scope is the caller's
`scope` bytes and whose label is the node ID's exact label. Declarations keep
their entity kind. The four annotation axioms keep their subjects and values.
The six class axioms keep their class expressions, object properties and
inverses. Original tokens are dropped.

FunctionalModel gives the independent correspondence as relations:
AnnotationModel and AnnotationsModel, ClassModel, MembersModel and RestModel,
ClassAxiomModel, AxiomModel and OntologyModel. Every mapping is proved total by
well-founded recursion on the size of the source records, and every result
satisfies its relation. The mapping returns no ontology only for a member list
with fewer than two members. The Shaped predicates record that minimum. The
mapping theorems prove that shaped records always map. The grammar theorems,
from class_run_shaped to tail_run_shaped, prove by structural recursion over the
derivations that the document grammar accepts only shaped records.

`source_reasoning::source_consistent`, `source_class_satisfiable` and
`source_subsumed` run the document reader, the mapping and the ontology-level
ALC query on the original bytes. SourceReasoning proves:

- read_document_read: every accepted document is read from the bytes. Its prefix
  header is parsed from the same bytes, the normative checker accepts its table,
  and the independent document grammar derives the rest with exactly those
  namespace rows;
- read_document_maps: every accepted document maps to a raw OWL ontology of the
  bytes (SourceOntology);
- the three `_correct` theorems: every call terminates; an error is exactly the
  reader's first error; every other result is the kernel's query on a raw OWL
  ontology of the bytes; and an answer equals Consistent, ClassSatisfiable or
  Subsumed of its axioms for any valid vocabulary;
- source_consistent_complete, source_class_satisfiable_complete and
  source_subsumed_sound: completeness, and soundness of a positive subsumption
  answer, in every universe.

No answer therefore means the axioms or the query are outside the supported ALC
fragment; the pipeline itself never declines a read document.

Three regressions in `crates/rowl-kernel/tests/source_reasoning.rs` cover:

- the five maintenance questions, answered from the original bytes;
- the model of a fixture that uses every record kind: identity with version, an
  import, a nested ontology annotation, plain-literal normalization, a
  declaration, a node-ID subject with its scope, an annotated `SubClassOf` with a
  three-member intersection in order, and the domain of an inverse property;
- a reader error passing through, an inverse-property domain giving no answer,
  and an unsatisfiable class in a consistent document.

The functional_class_axioms example now answers its questions with these
functions.

This block adds 38 public theorems and 22 independent definitions. Totals are
779 audited theorems, 593 definitions, 365 Rust regressions and 972 ledger
obligations. Individuals and assertions, the other axiom forms, anonymous scopes
across an import closure, the remaining constructors, datatypes and performance
remain pending.


## M3: Functional Syntax assertions

`functional_assertions::read_assertion` reads one `ClassAssertion`,
`ObjectPropertyAssertion` or `NegativeObjectPropertyAssertion`. In source order
it reads the keyword, `(`, the axiom annotations with the proved annotation
reader, the body, then `)`. A class assertion's body is a class expression and
an individual; a property assertion's body is an object property expression,
possibly `ObjectInverseOf`, and its source and target individuals. Class and
property expressions reuse the proved readers with the caller's class limits.
An individual is a full or abbreviated IRI, resolved through the checked prefix
table, or a node ID with its exact label; both use the class IRI limit.

FunctionalAssertions gives the independent grammar: IndividualRun for one
individual, EdgeRun for a property and its two individuals, BodyRun and
AxiomRun. Totality and exact result/error equivalence are proved, and
assertion_progress shows that an accepted assertion consumes at least its
keyword and its closing parenthesis.

The document loop now sends the three assertion keywords to this reader
instead of reporting them as unsupported. The model mapping turns a named
individual into its exact IRI and a node ID into an anonymous individual of the
caller's scope; a class assertion keeps the model of its class expression, and
a property assertion keeps its property expression. AssertionModel states the
correspondence, and the shape theorems extend to assertions, so every read
document still maps.

Three regressions in `crates/rowl-frontend/tests/functional_assertions.rs`
cover:

- every form, with named and anonymous individuals, inverse properties and
  axiom annotations;
- the unchanged suffix after an assertion;
- the first error at each step: a missing individual, a literal in an
  individual position, an undeclared prefix, an unsupported class expression,
  an extra individual and a keyword of another axiom form.

The end-to-end model test also checks a class assertion on a node ID and a
property assertion through an inverse property.

This block adds 24 public theorems and 13 independent definitions. Totals are
803 audited theorems, 606 definitions, 368 Rust regressions and 996 ledger
obligations. Reasoning with these assertions is the next step; the ALC queries
still give no answer for a document that contains them.


## Reasoner: ALC with named individuals

`abox::abox_satisfiable(count, facts, edges, axioms)` decides whether some
interpretation in which `axioms` holds at every element has elements for the
nodes `0..count` that satisfy `facts` (a concept at a node) and `edges` (a named
object property between two nodes). The completion:

1. adds the TBox concept at every node;
2. takes the pending facts one at a time and skips a fact already added;
3. otherwise adds it and expands a conjunction, branches on a disjunction, or
   pushes a universal restriction's filler to the target of every edge of its
   role from the node;
4. when nothing is pending, checks every node for a clash and decides every
   existential restriction with the TBox tableau, together with the fillers of
   the universal restrictions on its role at the same node.

`tbox::satisfiable_all` is the TBox tableau's entry point for such a list of
concepts; satisfiable_all_correct proves it like the single-concept entry point.

AboxTableau states the contract with AboxModel: an interpretation and an
assignment of elements to nodes in which the TBox concept holds everywhere and
every fact and edge holds. complete_correct proves the completion total by
well-founded recursion on (node and closure pairs not yet added, pending facts)
and exact against that contract. The invariant records, for every added fact,
what it requires of the added and pending facts; once nothing is pending, the
facts are saturated. model_of_saturated then builds the model: one element per
node and a disjoint copy of a successor model, chosen for every existential
restriction, whose root satisfies its filler and the universal restrictions on
its role. abox_satisfiable_correct is the public theorem; it needs a positive
count and facts and edges below it.

Three regressions in `crates/rowl-kernel/tests/abox.rs` cover the maintenance
inference with named individuals (pump1 hasPart motor1, motor1 is faulty, so
pump1 needs inspection), universal restrictions along edges in one direction
only, existential restrictions meeting universal ones, branching, the TBox
concept at every node, and an unsatisfiable TBox without facts.

This block adds 27 public theorems and 12 independent definitions. Totals are
830 audited theorems, 618 definitions, 371 Rust regressions and 1023 ledger
obligations. Using the completion for ontologies with assertions, and from
source text, is the next step.


## Reasoner: ontology queries with assertions

`alc_ontology::consistent`, `class_satisfiable`, `subsumed` and the new
`instance_of` now take axiom closures with `ClassAssertion`,
`ObjectPropertyAssertion` and `NegativeObjectPropertyAssertion`:

1. the class axioms become the TBox concept as before, and assertions impose
   nothing on it;
2. every individual an assertion mentions, named or anonymous, is interned into
   a node by exact structural equality (`same_individual_value`); node 0 stands
   for one more element;
3. a class assertion becomes its translated concept at its individual's node,
   and a property assertion an edge along its named property (an inverse
   property reverses the edge);
4. a negative property assertion contradicts the closure exactly when the same
   edge is asserted;
5. the query adds its concepts at node 0 (satisfiability, subsumption) or at the
   queried individual's node (instance checking) and runs the completion for
   named individuals.

Internalization now states its meaning for the axioms that are not assertions
(TBoxPart), and the completion's soundness theorem also says that its model
relates node elements only along the given edges, which negative assertions
need. AlcOntology proves every helper exact and then:

- closure_satisfiable_total: the check answers exactly when the closure is
  answerable (the internalization and translations succeed and everything is
  proper);
- closure_satisfiable_sound: an acceptance becomes an OWL model of the closure
  with every individual at its node and every query concept at its node;
- closure_satisfiable_complete: every OWL model, in any universe and with any
  reinterpretation of its anonymous individuals, forces acceptance;
- consistent_correct, class_satisfiable_correct, subsumed_correct and
  instance_of_correct: each answer equals Consistent, ClassSatisfiable,
  Subsumed or InstanceOf for any valid vocabulary, with the any-universe
  corollaries consistent_complete, class_satisfiable_complete, subsumed_sound and
  instance_of_sound.

SourceReasoning adds source_instance_of_correct and source_instance_of_sound,
so instance checks are proved end to end from the original bytes.

Regressions cover the maintenance inference with named individuals (pump1 needs
inspection, motor1 does not, an individual without assertions is an instance
only of what everything is), negative assertions through either orientation,
a class assertion that contradicts the TBox, anonymous individuals, built-in
properties in assertions, and the `maintenance-individuals.ofn` document read
and answered from its bytes. The `source_individuals` example shows the
end-to-end answers.

This block adds 35 public theorems and 12 independent definitions. Totals are
865 audited theorems, 630 definitions, 373 Rust regressions and 1058 ledger
obligations. `SameIndividual`, `DifferentIndividuals`, data assertions, the
other axiom forms, inverse roles and number restrictions remain pending.


## Reasoner: role inclusions and transitive roles (SH)

`tbox::satisfiable_with(concept, axioms, roles)` extends the TBox tableau to the
logic SH. A `role_box::RoleBox` lists inclusions `sub ⊑ sup` between named object
properties, which must include their compositions, and transitive named object
properties. `role_box::below` tests inclusion: equality or a listed inclusion,
comparing properties by exact spelling.

The tableau now works on item lists. An item is a concept of the input or a
`Through` item, the universal restriction `∀t.D` of a transitive property `t` on
a filler `D` of the input. When a successor along `s` is created, every universal
restriction `∀r.D` at the node, as a concept or a `Through` item, with `s` below
`r` requires `D`. For every transitive `t` with `s` below `t` and `t` below `r`,
it also requires the item `∀t.D`. Blocking compares items as the concepts they
stand for.

RoleBox defines what a role box means, independently of the Rust code: Respects
says that every listed inclusion and every listed transitivity holds. It proves
`below` exact. Hintikka now witnesses each existential with everything the
universal restrictions require along its role (roleFillers). Its model relates
two sets along a property when the second satisfies everything the first
requires along it. family_respects proves that this model satisfies every
listed transitivity, and every listed inclusion when the inclusions include
their compositions. TboxTableau proves every helper exact and `expand` total and
correct as before. The finite closure now also contains `∀t.D` for every
transitive `t` and every universal filler `D`.

satisfiable_with_correct and satisfiable_items_correct state the results. For a
role box closed under composition, every acceptance comes with a model of the
role axioms and the TBox concept with an instance. Every such model, in any
universe, forces acceptance. satisfiable_in and satisfiable_all run the same
procedure with no role axioms, and their theorems keep their statements.

Four new regressions cover:

- universal restrictions along included properties;
- paths along transitive properties and their sub-properties;
- blocked nodes that keep the restrictions of transitive properties;
- 300 pseudo-random concept and TBox pairs over two properties (`s` included in
  a transitive `t`), checked against every model of at most three elements.

This block adds 25 public theorems and 12 independent definitions. Totals are
890 audited theorems, 642 definitions, 377 Rust regressions and 1083 ledger
obligations. Reading role axioms from ontologies and source text, and using them
with named individuals, are the next steps.


## Reasoner: named individuals under role axioms

`abox::abox_satisfiable_with(count, facts, edges, axioms, roles)` runs the
completion for named individuals under a role box. Facts can now also be
`Through` facts, the universal restriction of a transitive property on a filler.
A universal restriction `∀q.D` at a node, as a concept or a `Through` fact,
reaches every edge `s(node, m)` whose property `s` is included in `q`. The target
`m` receives `D` and, for every transitive `t` between `s` and `q`, the fact
`∀t.D`. Each existential obligation is decided by the SH TBox tableau with
everything the universal restrictions at its node require along its role.
`abox_satisfiable` is the same procedure with no role axioms.

AboxTableau proves every helper exact and the completion total, as before. The
model of an acceptance has one element per node and a disjoint copy of a
successor model per obligation. A role relates two elements when one step along
an included property does, or a path of steps along the properties included in
a transitive property that it includes. roleModel_respects proves that this
model satisfies the closed role axioms without any assumption on the successor
models. node_truth follows a path along a transitive `t`: every element on it
has the filler and `∀t.D`, as a fact at a node or as truth in a successor
model. roleModel_entailed proves that node elements are related exactly as the
edges entail (Entailed: an edge along an included property, or a path of such
edges along a transitive property), which the check for negative property
assertions will use. abox_satisfiable_with_correct states the result, and
abox_satisfiable_correct keeps its ALC statement.

Three regressions cover universal restrictions along included properties,
transitive paths through named and anonymous parts, and 300 pseudo-random
two-node fact sets with edges, checked against every model of at most two
elements in which `s` is included in a transitive `t`.

This block adds 14 public theorems and 11 independent definitions, and retires
the concept-list entry point `tbox::satisfiable_all` (now `satisfiable_items`).
Totals are 901 audited theorems, 650 definitions, 380 Rust regressions and 1094
ledger obligations. Reading role axioms from ontologies and source text is the
next step.


## M3: Functional Syntax object property axioms

`functional_property_axioms::read_property_axiom` reads one object property axiom
with its axiom annotations at a caller-supplied position:

- `SubObjectPropertyOf`, whose sub-property is an object property expression or
  `ObjectPropertyChain( P1 P2 ... )` with at least two members;
- `EquivalentObjectProperties` and `DisjointObjectProperties`, with at least two
  members;
- `InverseObjectProperties`, with two properties;
- the seven characteristics `FunctionalObjectProperty`,
  `InverseFunctionalObjectProperty`, `ReflexiveObjectProperty`,
  `IrreflexiveObjectProperty`, `SymmetricObjectProperty`,
  `AsymmetricObjectProperty` and `TransitiveObjectProperty`, with one property.

Object property expressions, including `ObjectInverseOf`, use the proved reader.
Member lists stop before `)` and are bounded by the class limits' count; a list
or chain with fewer than two members is reported where the next member belongs.
FunctionalPropertyAxioms proves the reader total with exact result/error
equivalence to an independent grammar (PropertiesRun, ListRun, SubRun, BodyRun,
AxiomRun), and property_axiom_progress proves that every accepted axiom consumes
at least its keyword and its closing parenthesis.

The document loop now reads the eleven keywords instead of reporting them as
unsupported, and FunctionalDocument extends its grammar and proofs. The model
mapping turns the records into the raw OWL axioms of the same name, keeping each
chain and member list in source order. FunctionalModel proves the mapping exact
against PropertyAxiomModel and extends the shape invariants, so every read
document still maps. The ALC queries give no answer for these axioms yet.

New regressions read every form, the suffix after an axiom and each first error;
`maintenance-roles.ofn`, which declares a transitive `hasPart` with the
sub-property `hasComponent`, reads completely.

This block adds 28 public theorems and 16 independent definitions. Totals are
929 audited theorems, 666 definitions, 383 Rust regressions and 1122 ledger
obligations. Reasoning with these role axioms from source text is next.


## Reasoner: role axioms from ontologies and source text

The ontology queries now read role axioms. `alc_ontology::role_box` collects
`SubObjectPropertyOf` with a single named sub-property and a named
super-property, `EquivalentObjectProperties` of named properties and
`TransitiveObjectProperty` of a named property into a `RoleBox`. The completion
needs a role box closed under composition, so `add_inclusion` closes it while
inserting: `sub ⊑ sup` adds `x ⊑ y` for `x` equal to `sub` or listed below it
and `y` equal to `sup` or listed above it. An equivalence adds every member
below every member, and a transitivity appends its property.

The role axioms impose nothing on the TBox concept: Internalization supports
them, and the concept now holds everywhere exactly when every axiom that is
neither an assertion nor a role axiom (RoleAxiom) holds. OntologyRoles proves
every helper exact and states the result in role_box_correct: `role_box` always
terminates, its role box is closed under composition, and an interpretation
respects it exactly when it satisfies every role axiom of the closure
(RolesHold). The steps are closed_added (an insertion keeps a closed role box
closed), respects_added (the new role box is respected exactly when the old one
is and `sub` is included in `sup`) and equal_iff_included (equal relations are
mutual inclusions).

`closure_satisfiable` then runs `abox::abox_satisfiable_with` with this role
box. `roles_proper` also rejects built-in properties in role axioms, and a
negative property assertion next to a nonempty role box has no answer
(`has_negative`): it would have to be compared with the entailed edges rather
than the asserted ones. AlcOntology restates totality, soundness and
completeness. Soundness gets the role axioms back from the completion's model
through role_box_correct and carries them into the OWL model, which reads every
property other than the built-in ones as the completion's model does.
entailed_of_empty shows that without role axioms the entailed edges are the
asserted ones, so the denial check stays exact. Completeness obtains the
respected role box from any OWL model. The query theorems (consistent_correct to
instance_of_sound) and the source theorems in SourceReasoning keep their
statements and now cover role axioms.

Regressions cover parts of parts: pump1 needs inspection only when
`hasComponent ⊑ hasPart` and `hasPart` is transitive (or the two properties are
equivalent and `hasPart` transitive), and the matching subsumption holds only
with both role axioms. Property chains, inverse properties, built-in properties
in role axioms, `FunctionalObjectProperty` and negative assertions next to role
axioms get no answer. `maintenance-roles.ofn` is answered from its bytes, and
the `source_roles` example shows the answers.

This block adds 26 public theorems and 3 independent definitions. Totals are
955 audited theorems, 669 definitions, 386 Rust regressions and 1148 ledger
obligations. Inverse properties, property chains, negative assertions next to
role axioms and the other property characteristics remain pending.


## Reasoner: concepts and role hierarchies with inverse roles

The inverse-roles stage replaces the recursive tableaux by a completion graph
tableau, which inverse roles need because a successor can constrain its
predecessor. Its first part adds the input language.

`concepts::Concept` is a concept in negation normal form whose roles are object
property expressions, named or inverse. `concepts::translate` maps ALCI class
expressions to it, with the same structure as `nnf::nnf`, except that existential
and universal restrictions keep `ObjectInverseOf`. Concepts states the meaning
`denote`, reading roles with `objectRelation`, and proves
translate_total_correct: the translation terminates on every class expression,
returns `None` exactly outside ALCI (InAlci, since extended to InAlciq), and otherwise means the expression
(or its complement) in every interpretation fixing owl:Thing and owl:Nothing.
relation_inv shows that `inv r` relates exactly the reversed pairs of `r`.

`hierarchy::RoleHierarchy` lists inclusions between object property expressions
and transitive object property expressions. Hierarchy proves `below` and
`is_transitive` exact (below_correct, is_transitive_correct) and states
Respects, what the role axioms mean, and Closed: the inclusions include their
compositions and the inverse of every inclusion, and the transitive roles include
their inverses. The tableau will rely on Closed.

Three regressions cover inverse restrictions under De Morgan, role comparison by
orientation and spelling, and hierarchy tests.

This block adds 15 public theorems and 10 independent definitions. Totals are
970 audited theorems, 679 definitions, 390 Rust regressions and 1163 ledger
obligations. The concept table, the completion graph tableau with lazy unfolding
and clash detection on insertion, and the ontology queries with inverse roles
are next.


## Reasoner: the concept table

The completion graph tableau works on a table of interned concepts.
`concept_table::Entry` is one constructor whose parts are indices of earlier
entries; `intern` adds a concept and all its subconcepts, sharing every entry
that is already there, so equal subconcepts get one index and the tableau's
labels can be lists of indices. `close` adds `∀t.d` for every universal
restriction `∀q.d` in the table and every transitive role `t` included in `q`,
the restrictions the tableau passes along transitive roles, and `universal_from`
finds an entry `∀t.d`.

ConceptTable states the independent reading: WellFormed (every part comes
before its entry) and `meaning`, which rebuilds the concept of an index.
intern_correct proves that interning terminates, only appends, keeps the table
well formed and, when there is room, returns an index whose meaning is exactly
the interned concept; meaning_append shows that appending changes no meaning.
close_correct proves that closing only appends transitive restrictions of
existing universal restrictions and, when the inclusions include their
compositions, leaves the table TransitiveClosed; universal_found turns that
into a successful search.

Two regressions cover shared entries and the transitive restrictions of a role
and its inverse.

This block adds 11 public theorems and 7 independent definitions. Totals are
981 audited theorems, 686 definitions, 392 Rust regressions and 1174 ledger
obligations. The completion graph tableau is next.


## Reasoner: the completion graph tableau and its rule search

`completion::satisfiable` decides SHI with named individuals on a completion
graph. It interns the TBox concept, the facts and the lazy unfoldings `A ⊑ C`
into the concept table, closes it under the restrictions of transitive roles,
and starts with one node per named individual. Labels are lists of table
indices of literals. Conjunctions are split, disjunctions branch on a copy of
the graph, and inserting a literal whose complement is there is a clash on the
spot. `run` applies the first rule that `next_step` finds:

1. a node lacks something it needs: a fact, the TBox concept, or the concept of
   an unfolding whose class it lists;
2. an edge (a link between named nodes or a tree edge) lacks, at either end,
   what a universal restriction at the other end requires along its role,
   including `∀t.d` for every transitive role `t` in between;
3. an unblocked node has an existential restriction without a neighbour along
   an included role that satisfies its filler; a tree node is created.

A tree node is blocked when two tree nodes on its path to its named root have
the same label. `None` means that a structure would exceed the `usize` range.

CompletionSearch proves the search exact: `Holds` (propositional satisfaction of
an entry by a label) is decided by `holds`; every search returns an entry the
node needs and lacks (Needs), else an unblocked node with an existential
restriction that has no witness (Witnessed over Neighbour), else `Done` exactly
when no rule applies (Complete); `blocked` decides Blocked over the tree path.

Seven regressions cover inverse roles reaching predecessors, transitive inverse
roles along paths, cycles closed by blocking, lazy unfolding, inverse links
between named individuals, 400 pseudo-random inverse-free inputs that agree with
the verified SH tableau, and 400 pseudo-random inputs with inverse roles that
the tableau accepts whenever a model of at most three elements exists.

This block adds 23 public theorems and 18 independent definitions. Totals are
1004 audited theorems, 704 definitions, 399 Rust regressions and 1197 ledger
obligations. Termination, soundness and completeness of `run` are next.

## Reasoner: the completion graph tableau is total, sound and complete

CompletionModel reads a complete graph as a model, independently of how the
graph was built. Its elements are the named nodes and the labels of the
unblocked tree nodes. A named class holds where the label lists it. Two named
nodes are related along a role when a link's role, or the inverse of its role
for the reverse direction, is included in the role; every other pair is related
when the labels are Compatible: each satisfies what the other requires along the
role and along its inverse. A role also relates the ends of every path of such
steps along a transitive role included in it. The truth lemma shows that every
element satisfies every entry its label holds, and `model_of_complete` turns a
complete, clash-free graph of the right Shape into a model of the role hierarchy
in which the TBox concept and the unfoldings hold everywhere and every
requirement, link and named label holds. Without role axioms, named nodes are
related only along links.

Completion proves `run` total, sound and complete (`run_correct`, with `add`,
`branch`, `add_literal` and `create` in `add_correct`). For a table of `n`
entries, a node at depth `d` weighs `(2n+2)^(2^n+1-d)` times the room left in it
(`2n` minus its label and its witnessed existential restrictions). Adding a
literal shrinks that room; creating a child witnesses an existential at its
parent, which outweighs the whole new child, because equality blocking keeps
the labels on an unblocked path pairwise distinct (`path_distinct`) and so its
depth at most `2^n` (`depth_le`). An acceptance comes with NamedModel; a
rejection excludes FullModel, a model in any universes that places every node,
each tree node along the role that created it, so a clash on both branches of a
disjunction excludes both.

`satisfiable_correct` composes the setup: the TBox concept, the facts and the
definitions are interned (`intern_correct`, `intern_facts_correct`,
`intern_definitions_correct`), the table is closed under the restrictions of
transitive roles (`close_correct`), and every individual starts as a blank named
node (`named_nodes_correct`). For a closed role hierarchy, and facts and links
on the given individuals, `Some(true)` comes with a model that respects the
hierarchy, in which the TBox concept and every definition hold everywhere and
every fact and link holds; without role axioms, named individuals are related
only along links. `Some(false)` rules out every such model, in any universes.
`None` reports only a `usize` limit. Every theorem uses only propext,
Classical.choice and Quot.sound.

This block adds 74 public theorems and 23 independent definitions. Totals are
1078 audited theorems, 727 definitions, 399 Rust regressions and 1271 ledger
obligations. The ontology queries move to this tableau next, with inverse
property axioms and domains as universal restrictions on inverse roles.

## Reasoner: SHI ontology queries on the completion graph tableau

`shi_ontology` answers consistency, class satisfiability, subsumption and
instance checking on the completion graph tableau. The input contract:

- Class axioms over ALCI class expressions (SubClassOf, EquivalentClasses,
  DisjointClasses, DisjointUnion) and domains and ranges of object property
  expressions, named or inverse, with ALCI classes.
- Role axioms: SubObjectPropertyOf without chains, EquivalentObjectProperties,
  InverseObjectProperties, SymmetricObjectProperty and TransitiveObjectProperty,
  on named or inverse object properties.
- Class assertions, object property assertions (also along an inverse) and,
  without role axioms, negative object property assertions; declarations and
  annotation axioms impose nothing.
- No answer for any other axiom or class expression, for
  `owl:topObjectProperty` or `owl:bottomObjectProperty` anywhere, for negative
  assertions next to role axioms, or when a `usize` limit is reached.

ShiParts reads the class axioms as inclusions. An inclusion whose left side is
absorbable becomes a definition `A ⊑ C` that the tableau unfolds only at nodes
that list `A`: a named class directly, `∃r.E ⊑ D` as `E ⊑ ∀r⁻.D`, and
`E ⊓ F ⊓ … ⊑ D` as `E ⊑ ¬F ⊔ … ⊔ D`. Every other inclusion conjoins `¬C ⊔ D` onto
the TBox concept, and a domain or range conjoins `∀r⁻.C` or `∀r.C`, so neither
branches. `class_parts_correct` proves that in every interpretation fixing
owl:Thing and owl:Nothing the TBox concept holds everywhere and the definitions
hold exactly when every class axiom holds (PartsHold, ClassPart); the parts are
computed only for supported axioms (SupportedAxiom), and always when every
axiom is supported and the definitions fit (Inclusions bounds them).

ShiRoles builds the role hierarchy. Every inclusion is added with its inverse,
each together with its compositions with the inclusions already listed, and
inclusions the hierarchy already has are skipped; every transitive role is
added with its inverse. `role_hierarchy_correct` proves the result closed under
composition and inverses (`closed_both_added` carries the inverse closure over
both additions) and that an interpretation respects it exactly when it
satisfies every role axiom (RolesHold).

ShiOntology assembles the queries. Class assertions and the query's concepts
are facts at the nodes of their individuals, node 0 standing for one more
element, and object property assertions are links. Without role axioms, the
tableau's models relate named individuals only along links, so a negative
assertion is refuted exactly by a link in either orientation (Denies). An
acceptance is turned into an OWL model of the closure: built-in classes,
properties and the datatype map get their fixed meaning, and every other name
keeps the tableau's reading, which agrees on proper concepts (Proper,
DefinitionProper, RoleProper). `consistent_correct`, `class_satisfiable_correct`,
`subsumed_correct` and `instance_of_correct` prove each answer exact for the
Direct Semantics, and the `_complete` and `_sound` forms hold in any universes.

Eight regressions cover absorption, inverse properties reaching back,
symmetric and transitive inverse properties, domains and ranges of inverse
properties, negative assertions and unsupported inputs, 200 pseudo-random closures
whose parts are compared with the axioms in all interpretations of up to three
elements, 200 pseudo-random queries that must be satisfiable whenever such a
model exists, and 200 inverse-free closures that agree with the verified ALC
queries. On the full medication example (three patients, two drug classes,
disjointness and the alert rule) each query takes well under a millisecond;
the ALC queries, which branch on the alert rule at every node, were too slow
for it.

This block adds 61 public theorems and 11 independent definitions. Totals are
1139 audited theorems, 738 definitions, 407 Rust regressions and 1332 ledger
obligations. Answering from source bytes with these queries is next.

## Reasoner: SHI answers from source bytes

`source_reasoning` now runs the SHI queries: `source_consistent`,
`source_class_satisfiable`, `source_subsumed` and `source_instance_of` read the
document, map it into the raw model and call `shi_ontology`, as one extracted
unit. The document reader already reads `ObjectInverseOf` in restrictions and
the inverse, symmetric and other object property axioms, so SHI documents are
answered from their bytes. SourceReasoning's theorems keep their statements with
the SHI queries in place of the ALC ones: an error is exactly the reader's first
error, every accepted document reaches the query, and an answer is exact for
the Direct Semantics of the read axioms, complete in every universe.

The medication-safety example is the full one again: carol has the same allergy
as alice but receives a tablet with azithromycin, a macrolide, and macrolides
are disjoint from penicillins. The alert follows for alice only, and the
tablet's active ingredient is proved to be no penicillin. Absorption makes the
alert rule a definition on PenicillinAllergy, so the tableau branches only at
the two patients with that allergy. A new regression answers inverse,
symmetric and inverse-restriction questions from source bytes, and the stage's
example (`shi_ontology`) shows inverse, symmetric and transitive properties.

The theorem and definition totals are unchanged (1139 and 738); 408 Rust
regressions and 1332 ledger obligations.

## Reasoner: backjumping in the completion graph tableau

Every node now records the branch points its label depends on (`deps`). A rule
adds to a node with the points of the node and of its neighbours, its parent, its
children and the nodes linked to it (`rule_deps`), so the points cover whatever
the rule rests on; a new tree node starts with its parent's points; a clash
reports the points of its node and of the clashing entry; a pending `⊥` reports
the points of the entries it came from. A disjunction branches under a fresh
point `k`: the left disjunct is added depending on `k`. If it fails with a clash
set that does not contain `k`, the right disjunct would fail the same way and is
skipped; otherwise the right disjunct is added depending on the clash set
without `k`, and its failure is reported. The points are kept as lists;
joining skips points already listed (`join_from`), and `without_from` drops the
branch point.

Completion states what a rejection means with the points: FullModel now takes
the set `D` of a clash and asks only for the labels and tree edges of the nodes
whose points lie in `D`, and for the pending entries when their points do.
`add_correct` proves that a rejection with `D` rules out every such model and
that `D` lies below the next free point (FreshNodes). The branch case is the
backjumping argument: a clash set without `k` rules out the model whichever
disjunct holds, and a clash set from the right disjunct rules it out together
with the left failure, because the nodes' points lie below `k`. For the initial
graph every node has no points, so `satisfiable_correct` keeps its statement and
the ontology and source queries their theorems.

A new regression refutes an inconsistent TBox with eight individuals; with
chronological backtracking three individuals did not finish in two minutes.

This block adds 7 public theorems and 4 independent definitions. Totals are
1146 audited theorems, 742 definitions, 409 Rust regressions and 1339 ledger
obligations.

## Reasoner: reuse across queries

`shi_ontology::prepare` does once what every query did before its tableau run:
it collects the individuals, splits the class axioms into the TBox concept and
definitions, turns class assertions into facts and object property assertions
into links, builds the closed role hierarchy, checks that every name is
ordinary, and records whether a negative object property assertion is refuted
by a link. `PreparedData` states the result; `prepare_correct` proves that
`prepare` terminates and that whatever it returns satisfies `PreparedData`.

`prepared_satisfiable` adds only the query's own facts. The tableau entry point
`completion::satisfiable` now takes the query facts and the closure facts as
two lists (`intern_facts_correct` interns after any earlier facts) and copies
the prepared links (`copy_links`), so the prepared closure is never changed.
`prepared_sound` and `prepared_complete` carry the old closure theorems over to
a prepared closure, and `prepared_consistent`, `prepared_class_satisfiable`,
`prepared_subsumed` and `prepared_instance_of` are proved exact for the Direct
Semantics of the closure's axioms in any universes, with the same completeness
and soundness corollaries as the plain queries. The plain queries are now
`prepare` followed by the prepared query, and their statements are unchanged.

`source_reasoning::source_ontology` reads source bytes once: its error is
exactly the reader's first error, it never returns `Ok(None)`, and its ontology
is the raw OWL ontology of the bytes. `source_prepared` prepares that
ontology's axioms; `source_prepared_correct` gives a prepared closure that
satisfies `PreparedData` for the axioms of the bytes, so every prepared query on
it is exact for them. The medication-safety example now reads its document once
for its five questions; in a debug build the run takes under a second instead of
about five, because reading the document dominated.

`answer_supported`, `closure_satisfiable_sound`, `closure_satisfiable_complete`
and the `AnswerData` definition are replaced by `prepared_supported`,
`prepared_sound`, `prepared_complete` and `PreparedData`. Totals are 1158
audited theorems, 742 definitions, 411 Rust regressions and 1351 ledger
obligations.

## Reasoner: cardinality restrictions in concepts

The number restrictions stage starts with the input language. `concepts::Concept`
gains `AtLeast(n, r, C)` and `AtMost(n, r, C)`, which Concepts reads with the
independent OWL definitions: `AtLeast n P` is an injection of `n` elements
satisfying `P`, and `AtMost n P` is the absence of `n + 1` of them.
`concepts::translate` now covers ALCIQ (InAlciq): ObjectMinCardinality,
ObjectMaxCardinality and ObjectExactCardinality, with or without a filler, and
with cardinalities below `usize::MAX`, so that one more always fits. The
complement of a minimum `n` is a maximum `n - 1` (nothing for `n = 0`), the
complement of a maximum `n` is a minimum `n + 1`, and an exact cardinality is
the intersection of both bounds, or the union of their complements. The filler
keeps its polarity. translate_total_correct covers the new cases with the same
contract as before. `concepts::negate` builds the complement of any concept in
negation normal form; negate_correct proves that it means exactly the negation
in every interpretation.

`concept_table::Entry` gains the same two forms. A maximum restriction also
records the index of its filler's complement, interned with `negate`, because
the tableau must decide the filler at every neighbour that a maximum
restriction counts. The complement is not a part of the concept, so
intern_correct now recurses on the number of constructors (`size`), which a
complement does not increase (negate_size). intern_correct also proves that
interning keeps every maximum restriction recording its filler's complement
(Complements), which appending to a well-formed table preserves
(complements_append).

The completion graph tableau does not count: `completion::add` gives no answer
when a cardinality restriction would enter a label, and its theorems are
unchanged. The ontology queries decline concepts with cardinality restrictions
(`Proper`), so their answers and theorems are unchanged; the translation
fragment in their statements is now InAlciq. The completion forest that counts
comes next.

This block adds 6 public theorems and 5 independent definitions. Totals are
1164 audited theorems, 747 definitions, 415 Rust regressions and 1357 ledger
obligations.

## Reasoner: the completion forest and its rule search

Counting needs a different tableau. The completion graph's model relates any
two elements whose labels are compatible, which is harmless for existential and
universal restrictions but can give an element more neighbours than a maximum
restriction allows. `forest.rs` is a completion forest for SHIQ with named
individuals, in the style of Horrocks, Sattler and Tobies. Each named individual
has a root; anonymous nodes form trees below the roots, and the edge from a
parent to a tree node carries a list of roles. A tree node remembers the filler
it was created for (its seed) and which of its existential and minimum
restrictions it has expanded. Rules apply in a fixed order: missing concepts of
nodes and edges, the choose rule (every neighbour that a maximum restriction
counts decides its filler or the filler's complement), the merge rule, and the
expansion of existential and minimum restrictions at unblocked nodes, which
creates pairwise different tree nodes. When a maximum restriction counts more
neighbours than it allows, two of the first `n + 1` that are not known to differ
are merged, each pair in turn under one branch point with backjumping; when all
of them differ, it is a clash. A merge moves a tree node into a sibling, into
its grandparent or into a named node, or a named node into another one, along
with the roles of its edge and its differences, and prunes its subtree.
Blocking is pairwise, as counting with inverse roles requires: a tree node is
blocked when its label, its parent's label and the roles between them repeat
higher up on its path. Number restrictions must be on simple roles.

ForestSearch proves the rule search exact. neighbours_correct shows that the
neighbour list of a node along a role contains exactly its neighbours
(Neighbour), each once: active children along an included role, the parent
along an included inverse role, and the named nodes that a link or an added
edge relates to it, read through the merges of named nodes. next_step_correct
shows that the search returns a concept that an active node lacks and that its
requirements, the TBox concept, an unfolding, its seed or an edge requires
(AddNeeds); else a neighbour to decide; else a maximum restriction with too many
neighbours (Excess); else a restriction to expand at an unblocked node; and that
it reports Done exactly for a complete forest (Complete). blocked_correct shows
that `forest::blocked` decides pairwise blocking (Blocked).

Randomized regressions compare the forest with the completion graph on inputs
without counting, check that every concept, and every set of facts and links
about three individuals, that has a model with at most three elements is
accepted, and check that random inputs with counting always get an answer.

This block adds 37 public theorems and 24 independent definitions.

## Reasoner: the completion forest's run

ForestOps proves the operations the rules apply exact: copying, adding an item
to a label, creating children with their differences, the branch points a rule
rests on, the pairs of counted neighbours not known to differ and their
orientation, and the parts of a merge, which move the roles of a merged child
onto the parent edge or a sibling, add edges between named nodes, rename an
individual's representative, inherit differences and prune the merged subtree.
The merge and the expansion of a restriction are separate functions
(`forest::merged`, `forest::expanded`) so that their structure is proved apart
from the recursion.

ForestInv defines the invariant `run` keeps (Inv): a well-formed table whose
maximum restrictions record the complements of their fillers and count along
simple roles, closed under the restrictions of transitive roles; roots exactly
for the named individuals and every individual read through the merges as an
active root; active tree nodes below active parents with smaller indices;
clash-free labels of literals without repetitions; the expanded restrictions
among the label; and edge roles among the roles of the existential and minimum
restrictions and their inverses. The termination measure weights every active
node by `base^(bound + 2 − depth)` times the room left in its label and its
expanded restrictions, where `bound` counts the different labels, parents'
labels and role sets; pairwise blocking keeps the depth of an unblocked node
within `bound` (depth_le_bound). A model of a forest under a set of branch
points (Models) places every node in an interpretation that respects the role
hierarchy, where the TBox concept and the unfoldings hold everywhere, the
requirements and links hold for the individuals, each individual sits where its
representative does, and labels, tree edges and seeds, added edges and
differences hold when the points they depend on are in the set.

ForestSteps proves the two structural steps. Expanding a restriction keeps the
invariant, costs the node more weight than all its new children carry
(created_measure), and a model of the restriction provides different witnesses
for the children (created_models). A merge, oriented as `forest::orient` does
(orient_shape), keeps the invariant, removes the merged node from the measure,
and a model that places both nodes on one element models the merged forest
with the merged node's label at its target (merged_models).

Forest proves the run. run_correct: on every forest that keeps the invariant,
`run` terminates; an acceptance comes with a complete forest that keeps the
invariant, and a rejection with branch points below the next free one rules
out every model, in any universes, under those points. branch_correct covers
both the disjunction and the choose rule, retrying the second alternative only
when the first failure depends on the new branch point. merge_rule_correct
shows that in every model of a maximum restriction with too many counted
neighbours two of its first `n + 1` neighbours coincide, so that some pair not
known to differ is merged; choices_correct tries those pairs in turn and
accumulates the branch points of the failures that depend on the choice.
satisfiable_answers shows that `forest::satisfiable` answers unless a structure
would exceed the `usize` range or a number restriction counts along a role that
is not simple, that false answers rule out every model of the role hierarchy,
the TBox concept, the definitions, the facts and the links, and that true
answers come with a complete forest that keeps the invariant for the interned
input; the next block turns that forest into a model.

This block adds 127 public theorems and 40 independent definitions. Totals are
1330 audited theorems, 811 definitions, 425 Rust regressions and 1523 ledger
obligations.

## Reasoner: the model of a complete forest

ForestModel builds a model from any complete forest that keeps the invariant,
independent of how the forest was built: its unravelling under pairwise
blocking, as in Horrocks, Sattler and Tobies. The elements are the paths from an
active named node through active children, newest pair first; a pair holds the
child and the node it stands for, which is the child itself unless the child
repeats the label, the parent's label and the roles of a node on its parent's
path, and then that node (holder). The newest node of a path is always active
and unblocked, and the node a child stands for has the child's label and roles
and a parent with the label of the path's previous node (path_shape). A named
class holds where the label of the newest node lists it; a role relates a path
to its extension along a role of the child's edge, the extension back to the
path along an inverse, and named nodes along the links and added edges read
through the merges, closed under the transitive roles it includes.

The neighbours of a node in the forest and the neighbours of a path correspond
one to one with the same labels: every forest neighbour has a neighbour path
(step_of_neighbour), every neighbour path comes from a forest neighbour
(neighbour_of_step), and neither side has two partners (corr_unique,
corr_function). With that, the truth lemma (truth) shows that every path
satisfies every entry its label satisfies. A minimum restriction gets distinct
witnesses from the neighbours the complete forest has. For a maximum
restriction, which counts along a simple role, every counted element is a step
away; its forest neighbour decides the filler by the choose rule, and the
complement is excluded since it means the filler's negation; so more elements
than allowed would give more forest neighbours than allowed, which a complete
forest does not have. model_of_complete adds the role hierarchy, the TBox
concept, the unfoldings, the requirements and the links, and
satisfiable_correct shows `forest::satisfiable` exact: its true answers come
with a model in `Type` of the role hierarchy where the TBox concept and every
definition hold everywhere and every fact and link holds, and its false answers
rule out every such model, in any universes. No ontology query uses the forest
yet.

This block adds 31 public theorems and 11 independent definitions. Totals are
1361 audited theorems, 822 definitions, 425 Rust regressions and 1554 ledger
obligations.

## Reasoner: number restrictions in ontology queries

The ontology queries (`shi_ontology`) now count. Class expressions translate to
ALCIQ concepts, so minimum, maximum and exact cardinalities, qualified or not,
reach the TBox concept, the definitions and the facts; a functional object
property conjoins `≤1 r.⊤` onto the TBox concept and an inverse functional one
`≤1 r⁻.⊤` (ShiParts proves both against the OWL definitions, through
atMost_one_iff). Properness still rejects built-in classes and object
properties, now also inside number restrictions.

A prepared question goes to the completion forest when the closure or the
question counts (closure_counts, question_counts), and to the completion graph
tableau otherwise, so the answers and the speed of counting-free questions are
unchanged. The forest merges individuals that a maximum restriction forces
together, so the link test for negative object property assertions no longer
applies: a question that counts gets no answer next to a negative assertion.
prepared_sound and prepared_complete cover both tableaux: an acceptance by
either comes with an OWL model of the closure (owl_model_agrees now also
covers number restrictions, counting lifted elements with atLeast_lift), and
every OWL model forces acceptance by either. The consistency, satisfiability,
subsumption and instance theorems, and the queries from source bytes, keep
their statements and now cover SHIQ. A number restriction along a role that
includes a transitive role gets no answer.

This block adds 7 public theorems and 1 independent definition. Totals are 1368
audited theorems, 823 definitions, 426 Rust regressions and 1561 ledger
obligations.


## M3: individual equalities, enumerations and value restrictions

The reader now takes the four forms that name individuals: `SameIndividual`
and `DifferentIndividuals` as assertions, and `ObjectOneOf` and
`ObjectHasValue` as class expressions. Individuals have their own proved
reader (`functional_individuals`): an IRI resolved through the checked prefix
table or a node ID with its exact label, as before, and individual lists, the
maximal individual sequence before `)` with the member-count bound checked
before each further member, followed by the caller's minimum length. An
equality or inequality needs two individuals and an enumeration one; a shorter
list expects an individual where it stops. The class-expression and assertion
readers wrap its errors (`ClassError::Individual`, `AssertionError::Individual`),
which replaces the assertion reader's own individual errors, and an
enumeration or a value restriction uses one nesting level like the other
connectives. FunctionalIndividuals proves the individual grammar exact, and
FunctionalClasses, FunctionalAssertions and FunctionalDocument extend their
grammars and proofs; the document loop now sends both equality keywords to the
assertion reader.

The model mapping carries the anonymous-individual scope into class
expressions, since enumerations and value restrictions may name node IDs.
Enumerations map to `ObjectOneOf` with their individuals in order, value
restrictions to `ObjectHasValue`, and equalities and inequalities to
`SameIndividual` and `DifferentIndividuals` (EnumerationModel,
IndividualMembersModel). The independent shape invariants now require one
individual in each enumeration and two in each equality or inequality, which
the grammar guarantees, so every read document still maps. The OWL 2 position
restrictions on anonymous individuals in these forms stay the separate
`anonymous` check. The reasoner does not answer questions about these forms yet:
the ontology queries return no answer for them.

This block adds 17 public theorems and 7 independent definitions. Totals are
1385 audited theorems, 830 definitions, 428 Rust regressions and 1578 ledger
obligations.

## Reasoner: equal and different individuals

The ontology queries (`shi_ontology`) now decide `SameIndividual` and
`DifferentIndividuals`. Every member of either axiom gets a node after the
individuals of the assertions (members_from), and `prepare` unites the nodes of
the members of each equality: every node starts as its own representative
(identity_from), and uniting two nodes replaces the representative of the
second by that of the first everywhere (relabel, unite). ShiEquality proves the
result a union of classes (Joins): every representative is a node joined to its
own node by a chain of equalities, the equivalence closure of the positions of
members of one `SameIndividual` axiom, and the members of every equality share
their representative. So every OWL model of the closure gives a node and its
representative one element (representative_value, placement_representative),
and the facts, links and the check of negative assertions use the
representatives' nodes (node_of). An inequality two of whose members share a
representative, counting occurrences, refutes the closure (clash_from), which
every question then answers with `false`.

The completion graph tableau's models are now proved to keep different named
nodes apart (model_of_complete, satisfiable_correct), so without a shared node
every `DifferentIndividuals` axiom holds in the OWL model of an acceptance. The
completion forest merges named nodes when a maximum restriction requires it, so
a question that counts gets no answer next to a `DifferentIndividuals` axiom
yet; the nominal forest of a later step will decide it. prepared_sound builds
the OWL model with every individual at its representative's element, and
prepared_complete shows that every OWL model forces acceptance, now also when
equal individuals share a node. `PreparedData` became a structure with named
fields. The consistency, satisfiability, subsumption and instance theorems,
and the queries from source bytes, keep their statements.

This block adds 22 public theorems and 9 independent definitions. Totals are
1407 audited theorems, 839 definitions, 430 Rust regressions and 1600 ledger
obligations.

## Reasoner: nominals in concepts and the concept table

The concepts (`concepts::Concept`) gain the nominal `{a}` of an individual and
its complement `¬{a}`, which Concepts reads with the individual's meaning in
the OWL interpretation. `concepts::translate` covers ALCIQO: an enumeration
becomes the union of the nominals of its individuals, or the intersection of
their complements for the complement, and a value restriction `∃r.{a}`, or
`∀r.¬{a}` for the complement (one_of_correct, has_value_correct). The supported
fragment is now `Translatable`, the former InAlciq with enumerations and value
restrictions, and translate_total_correct keeps its form. `negate` and the
copies are proved for nominals.

The concept table interns `{a}` and `¬{a}` as entries compared structurally,
and rebuilds them exactly. Both tableaux treat a nominal that reaches a label
as outside what they decide: the completion graph tableau gives no answer, like
for cardinality restrictions, and so does the completion forest until it has
its nominal rules; their invariants keep nominals out of labels, so their
models and theorems are unchanged. The ontology queries reject nominals as not
proper, and the reinterpretation of anonymous individuals now speaks of proper
concepts (denote_with_anonymous), so the query proofs read their concepts in the
OWL model itself and translated_meaning is no longer needed.

This block adds 1 public theorem and removes 1. Totals are 1407 audited
theorems, 839 definitions, 431 Rust regressions and 1600 ledger obligations.

## Reasoner: the nominal rule of the completion forest

The completion forest (`forest.rs`) now takes nominals into its labels: `{a}`
and `¬{a}` are literals, and a label with both is a clash (complementary). The
named node of an individual is the representative of the node of the first
requirement with its nominal (forest::nominal_root, NominalRoot); it is keyed by
the individual, so equal nominals at different entries of the table share it.
After the missing concepts, the rule search looks for an active node whose label
has a nominal whose named node is another node (forest::nominal_node, proved
exact by nominal_node_correct). It gives no answer when the individual of a
nominal, or of the complement of one, in the label of an active node has no
named node. A complete forest (Complete) now also has every nominal of an active
node on the named node of its individual (NominalOkAt).

The nominal rule (forest::nominal) merges the node into the named node: a named
node directly, a child of a named node through its parent, while a nominal
below a tree node gives no answer. Every model under the branch points of both
nodes places them on the individual, since the label of the node and the
requirement of the named node both have the nominal; so a recorded difference
between them is a clash, and the merge, whose rejections rule out models that
keep the two apart, is forced (nominal_correct). The merge decreases the measure
as before, so the run keeps terminating.

The model of a complete forest places an individual with a named node on the
path of that node (nominalPlace). A path whose label has `{a}` is that path,
since a nominal is only on the named node of its individual, which is a named
node and so never a tree node of a longer path; a path whose label has `¬{a}`
is not, since the named node of `a` also lists the nominal of its requirement,
which would clash (truth). satisfiable_correct keeps its statement, now for
labels with nominals. The ontology queries still reject nominals as not proper.

This block adds 9 public theorems and 5 independent definitions. Totals are
1416 audited theorems, 844 definitions, 433 Rust regressions and 1609 ledger
obligations.

## Reasoner: nominals in the ontology queries

The ontology queries (`shi_ontology`) now take nominals. A concept is proper
when its nominals are of named individuals (IsNamed), which a reinterpretation
of the anonymous individuals leaves in place (denote_with_anonymous). The
individuals of the nominals of the TBox concept, the definitions and the class
assertions get nodes after the other individuals (ShiNominals:
nominal_individuals_correct, definition_individuals_correct,
assertion_individuals_correct), before the representatives are computed. A
question's nominals must be of individuals the closure has (facts_known).

A question goes to the completion forest when it counts, has a nominal, or is
about a closure with negative assertions next to role axioms (question_forest,
tangled); every other question goes to the completion graph tableau as before.
The forest gets, besides the facts of the class assertions, the nominal `{a}` of
every individual at its node (named_from_correct), the members of every
`DifferentIndividuals` axiom outside the nominals of the later members
(apart_members_correct, unequal_from_correct), and `∀r.¬{b}` at the node of `a`
for every negative assertion `¬r(a, b)` (refused_from_correct). `PreparedData`
records where each of these facts comes from and that every individual,
inequality and negative assertion has its facts.

prepared_sound reads the forest's model: the nominal fact of an individual puts
the individual where its node is, so the OWL model built from the forest's
model agrees with it on proper concepts whose nominals' individuals have nodes
(owl_model_agrees, now with that agreement as a hypothesis); an inequality's
complements keep its members apart and a negative assertion's restriction keeps
its individuals unrelated. prepared_complete shows that every OWL model of the
closure satisfies these facts, so it forces acceptance as before. The
consistency, satisfiability, subsumption and instance theorems, and the queries
from source bytes, keep their statements; inequalities and negative assertions
next to counting or role axioms are now answered, and so are enumerations and
value restrictions of named individuals.

This block adds 21 public theorems, removes 2, adds 3 independent definitions
and removes 1. Totals are 1435 audited theorems, 846 definitions, 435 Rust
regressions and 1628 ledger obligations.

## Reasoner: nominals below anonymous elements

The nominal rule of the completion forest (forest::nominal) now merges a node
whose label has `{a}` into the named node of `a` at any depth, not only a named
node or a child of one. A merge (forest::moved) hands the edge of a merged tree
node over to its grandparent or to a sibling as before, and otherwise, when the
target is a named node, adds edges from the merged node's parent, which may now
be a tree node, to the target; the merged node's own added edges move to the
target (forest::carried, carried_correct, CarriedEdge, moved_carried). The shape
of a forest (Shape) allows added edges from tree nodes to named nodes, and the
shape of a merge (MergeShape) covers the merge of any node into a named node.

Added edges count only from live nodes, active and not blocked (Live,
forest::live, liveEdges): the neighbours, the needs of edges and the
completeness of a forest read only those. Pairwise blocking now only repeats
tree nodes whose parent is a tree node (SamePair), so the node that a blocked
node stands for never has a named parent that an added edge could reach too,
and the depth of an unblocked node is at most one more than the number of
different pairs (depth_le_bound).

The model of a complete forest relates paths by their newest nodes along links
and added edges (Step), so every path of a live tree node with an added edge to
a named node is a neighbour of the path of that node, and every live node has a
path (live_path). Every neighbour path still comes from one neighbour
(corr_function), and a neighbour has one neighbour path unless it is a tree node
that an added edge relates to a named node without being its child (corr_unique,
corr_third). The model may repeat such a node, so the maximum restrictions of a
named node must not count it: the rule search gives no answer when one does
(Repeated, Unrepeated, forest::repeated_satisfying), a complete forest has no
such count (CountOk), and the truth lemma relies on that. satisfiable_correct
keeps its statement; the forest and the ontology queries now answer questions
whose nominals reach anonymous elements below others, apart from that count.

This block adds 18 public theorems and 5 independent definitions. Totals are
1453 audited theorems, 851 definitions, 436 Rust regressions and 1646 ledger
obligations.

## Reasoner: named nodes beyond the individuals

A step toward new named nodes in the completion forest. A named node is now any
node that is no tree node (Named), not only the node of an individual: the
invariant keeps a named node for every individual, every individual read
through the merges as an active named node, and every end of an added edge an
individual, read through the merges, or an active named node (NamedEnd). A
merge of a named node into another one now also relinks the added edges at the
merged node to its target, which then also depend on the merge
(forest::relink, forest::relinked, relinked_correct, RelinkedEdge), so no added
edge ends at an inactive named node; edges at individuals were already read
through their representatives. The model of a complete forest starts its paths
at every active named node. No rule creates further named nodes yet, so the
answers are unchanged.

This block adds 13 public theorems and 3 independent definitions. Totals are
1466 audited theorems, 854 definitions, 436 Rust regressions and 1659 ledger
obligations.

## Reasoner: new named nodes for counting through nominals

A maximum restriction `≤n r.C` of a named node must not count a tree node that
is not its child, since the model may repeat that node. The completion forest
no longer gives up there: the rule for new named nodes (forest::name_rule,
forest::guesses) guesses the number of neighbours along `r` that satisfy `C`,
from 1 to `n`, and creates that many new named nodes (forest::named,
forest::fresh_named, NamedMade): each with the seed `C`, an added edge from the
node along `r`, pairwise different, and the guess as a bound on those
neighbours (Cap, CapHolds). Once the bound exists, the rule (forest::capped_rule)
merges the tree node with one of the first `bound` counted named neighbours,
trying each pair not known to differ in turn. New named nodes get their seed
like tree nodes (Seeded, forest::seeded), and a model of the forest gives
seeds and bounds their meaning (Models).

Every model of the restriction has an exact number of counted neighbours
between 1 and `n` (exactly_between), so a rejection of every guess rules out
every model, and a guess that a failure does not depend on is not retried
(guesses_correct, named_rejected, name_rule_correct). With the bound, the
counted named neighbours and the tree node are `bound + 1` neighbours in every
model of the bound, so two of them coincide (capped_rule_correct). The run
terminates because the measure now adds, for every maximum restriction of a
named node without a bound, a weight that is the larger the earlier the node
(nameWeight, nameUnit, nameBase); new named nodes come after the node that made
them, so they and their own restrictions weigh less than the restriction that
got its bound (named_measure), and every other step keeps that weight
(nameWeight_eq, nameWeight_append). Named nodes may now be merged into each
other with their added edges relinked, which the previous block proved.

The forest now answers every random input of the tests with nominals of named
individuals, also those whose models are infinite chains collapsing onto a
named node's bounded neighbours, and the ontology queries decide maximum
cardinalities of individuals that anonymous elements reach through value
restrictions. No answer remains only when a bound has fewer counted named
neighbours than it allows, which the tests never reach.

This block adds 34 public theorems and 11 independent definitions. Totals are
1500 audited theorems, 865 definitions, 438 Rust regressions and 1693 ledger
obligations.

## Reasoner: self restrictions in the concepts

The concepts of the tableaux now have the self restriction `∃r.Self` and its
complement `¬∃r.Self` (concepts::Concept::HasSelf, NotSelf), which hold exactly
at the elements that `r` relates, or does not relate, to themselves.
concepts::translate turns `ObjectHasSelf(r)` into `∃r.Self`, and into
`¬∃r.Self` for the complement (concepts::self_restriction,
self_restriction_correct), so the translation covers ALCIQO with self
restrictions (Translatable) and is proved total and exact as before;
concepts::negate swaps the two, and copying is exact. The concept table interns
both as entries compared structurally, and a self restriction next to its
complement along the same role is a clash in both tableaux (Complementary).

Neither tableau has self loops yet: the completion graph tableau and the
completion forest give no answer when a self restriction reaches a label, and
the ontology queries treat a concept with a self restriction as not proper
(Proper), so they give no answer for it. The next blocks give the completion
forest self loops and the role characteristics that rest on them.

This block adds 1 public theorem. Totals are 1501 audited theorems, 865
definitions, 438 Rust regressions and 1694 ledger obligations.

## Reasoner: self restrictions in the completion forest

The completion forest now decides self restrictions. A self restriction
`∃s.Self` in the label of a node is a loop, an edge from the node to itself
along `s`, read from the label (SelfAlong, forest::looping, forest::self_along):
the node is its own neighbour along every role that includes `s` or its inverse
(forest::loops_along, the fifth part of forest::neighbours). Universal
restrictions pass along a loop in both directions like along any edge
(LoopNeeds, LoopsOk, forest::missing_loop, forest::missing_loops), and a node
with `¬∃r.Self` that is its own neighbour along `r`, through a loop, a link or an
added edge, is a clash (Looped, forest::looped_from, forest::looped_node,
`Step::Loop`), proved by the neighbour's relation in every model of the forest
(neighbour_holds). Self restrictions and their complements are literals of the
labels, so they are counted, chosen and merged like any other entry, and a node
with a loop counts itself among its neighbours.

The model of a complete forest relates a path to itself along the loops of its
newest node (the fifth case of Step, selfAlong_inv), and a path corresponds to
itself only for its own newest node (corr_tail, corr_loop), so every neighbour
still has one neighbour path. The truth lemma covers `∃s.Self` by the loop and
`¬∃r.Self` by the clash rule: complements of self restrictions, like number
restrictions, must be on simple roles (SimpleCounting, CountsSimply), so the
model relates a path to itself along `r` only through a step, which only a
neighbour of the newest node gives.

A loop can make a tree node its own neighbour next to its child or parent; a
maximum restriction may then have to merge the child into its parent, which no
merge does yet. The merge rule gives no answer at such a pair (LoopedPair,
forest::looped_pair, orient_either), while merging a tree node into a named
parent, which a loop at a named node calls for, was already proved. The
ontology queries now take `ObjectHasSelf` and reflexive and irreflexive object
properties, as `∃r.Self` and `¬∃r.Self` in the TBox concept, and decide them
with the forest; the tests answer all but one of 300 random inputs with self
restrictions and reflexive, irreflexive and functional properties, and every
class with a model of at most three elements comes out satisfiable.

This block adds 12 public theorems and 5 independent definitions. Totals are
1513 audited theorems, 870 definitions, 440 Rust regressions and 1706 ledger
obligations.

## Reasoner: merges into a tree parent

A loop can make a tree node its own neighbour next to its tree child or its
tree parent, and a maximum restriction may then have to merge the child into
its parent, which the previous block left without an answer. The merge rule
now orients such a pair as the merge of the child into its parent
(forest::orient, orient_shape, orient_either), a new case of a merge
(MergeShape) that keeps the edges as they are (forest::moved, moved_refl) and
carries the added edges of the child over as before. The edge between the two
becomes loops of the parent: the merge adds to the parent's label, after the
label of the child, the self restriction for a loop along each role of the edge
(IntoParent, forest::into_parent, forest::loop_for, forest::loop_entry,
forest::loops_of), and every model where the two nodes coincide relates the
parent to itself along those roles, so the rejections stay sound
(merge_correct). The table has these self restrictions: forest::satisfiable
interns the self restriction of the role of every existential and minimum
restriction before closing the table (forest::loop_entries,
loop_entries_correct), and the roles of every edge are among those roles and
their inverses, whose loops the same self restrictions are.

The guard of the previous block (LoopedPair, forest::looped_pair) is gone, and
the tests now answer every one of 300 random inputs with self restrictions and
reflexive, irreflexive and functional properties, also below anonymous elements
where a loop meets a successor along a functional property.

This block adds 6 public theorems and 1 independent definition and removes the
guard's theorem and definition. Totals are 1518 audited theorems, 870
definitions, 440 Rust regressions and 1711 ledger obligations.

## Reasoner: asymmetric and disjoint object properties

The role hierarchy now lists disjoint pairs of object property expressions
(hierarchy::Disjoint), which no pair may be related by together (Constrained).
The role axioms of a closure give them (shi_ontology::constraints_from,
ConstraintsHold): an `AsymmetricObjectProperty` is the pair of the property and
its inverse, and a `DisjointObjectProperties` axiom the pairs of every member
with every later one (shi_ontology::add_disjoint_members,
shi_ontology::roles_apart, shi_ontology::apart_with). The pairs are computed
apart from the inclusions and added to the hierarchy that the inclusions give
(shi_ontology::role_hierarchy), so an interpretation respects the hierarchy
exactly when it satisfies the role axioms and keeps the pairs apart exactly
when it satisfies the asymmetric and disjoint object properties
(role_hierarchy_correct). The class parts leave both axioms to the hierarchy
(ConstraintAxiom).

The completion forest treats a node with a common neighbour along both roles of
a pair as a clash (Overlap, forest::common, forest::overlap_from,
forest::overlap_node, `Step::Overlap`), since every model relates the node to
that neighbour along both roles (neighbour_holds). Its models keep the pairs
apart (a new part of Models), and the model of a complete forest does too: when
both roles are simple (SimpleCounting, forest::disjoint_simple), a pair of
paths related along both is a step along each, whose neighbours of the newest
node coincide (corr_function), and a complete forest has no Overlap
(model_constrained). With an asymmetric property, a loop is such a common
neighbour, so asymmetry also refutes self restrictions along the property.

The ontology queries take both axioms (with their roles not built in,
RoleProper) and route every closure with disjoint pairs to the forest
(shi_ontology::constrained); its acceptances come with an OWL model that
satisfies the axioms (owl_model_constraint_axiom), and every OWL model of the
closure keeps the pairs apart, so the rejections stay exact. Disjoint pairs on
roles that are not simple get no answer. This completes the stage: self
restrictions and reflexive, irreflexive, asymmetric and disjoint object
properties are decided with proofs, and of the role constructs of SROIQ only
role chains and the universal and empty roles (owl:topObjectProperty,
owl:bottomObjectProperty) remain.

This block adds 13 public theorems and 4 independent definitions. Totals are
1531 audited theorems, 874 definitions, 442 Rust regressions and 1724 ledger
obligations.

## Reasoner: role chains for the completion forest

The fifteenth stage adds the complex role inclusions `r1 ∘ … ∘ rn ⊑ r` of
SROIQ. Its first block decides them for the completion forest through an
encoding, leaving the forest and its proofs untouched; the ontology queries
take the chain axioms in the next block.

A role is complex when the role of a chain is included in it (Complex,
role_chains::complex). Every complex role `c` has an automaton (Trans,
role_chains::transitions, transitions_correct): from its initial to its final
state along `c`, and along every complex role strictly included in `c`; back
from the final to the initial state for a transitive role or a chain of two
roles equivalent to `c`; and for every other chain whose role is equivalent to
`c` a segment of new states along its roles, back to the final state when its
first role is equivalent to `c`, back to the initial state when its last role
is, and from the initial to the final state otherwise (segOf,
role_chains::segment). In every model of the role hierarchy and the chains an
automaton accepts exactly the pairs its role relates (accepts_initial,
accepts_of_rel).

A universal restriction `∀c.C` on a complex role becomes a fresh class, the
atom of the automaton's initial state with the filler `C`, and every atom gets a
definition that the forest unfolds lazily (role_chains::encode,
role_chains::unfold, role_chains::generate): the filler at the final state and,
for every transition, the atom of its target with the same filler, behind
`∀c.` for an edge along `c`, behind `∀s.` along a role `s` that is not complex,
nested in the atom of the initial state of a complex role `s`, and plainly for
a return. In the filler of a maximum restriction, where a concept stands in a
negative position, an existential restriction on a complex role becomes the
complement of the atom for the complement of its filler (Enc). The atoms are
named by a space and the eight bytes of their index (nameOf, nameOf_injective),
and no class of the problem may start with a space. The table keeps its atoms
distinct and lets fillers mention only earlier atoms (TableOk), and a bound of
2^20 atoms ends the encoding of a hierarchy that is not regular without an
answer.

Both directions are proved model-theoretically. A model of the role hierarchy
and the chains becomes a model of the encoding once each atom holds where every
path that its automaton reads leads into its filler (withAtoms, enc_sound,
atom_defined). Conversely, the relations that the inclusions, the transitive
roles and the chains derive from a model of the encoding (Stage, Closure) form
a model of the role hierarchy and the chains (closureModel, accept_model):
roles that no chain reaches keep their relations (stage_simple), so number
restrictions, self restrictions and their complements, and disjoint pairs,
which must be on such roles, keep their meaning, and the atoms carry their
fillers along every derived pair (stage_atoms, enc_complete). With the chains
completed by their mirrors (role_chains::copy_chains, Closes),
role_chains::satisfiable answers as forest::satisfiable with the chains as
further role axioms: its acceptances come with a model of the hierarchy, the
chains and the disjoint pairs, and its rejections rule out every such model
(Rowl.Chains.satisfiable_correct). Without chains it is the forest itself. The
tests decide uncle chains, left and right recursive chains, inverse paths,
chains through inclusions and named individuals, and every one of 300 random
concepts over two chains, all with a model of at most three elements coming out
satisfiable.

This block adds 111 public theorems and 30 independent definitions. Totals are
1642 audited theorems, 904 definitions, 450 Rust regressions and 1835 ledger
obligations.

## Reasoner: role chains in the ontology queries

The ontology queries now read every `SubObjectPropertyOf` with an
`ObjectPropertyChain` (ChainAxiom), its roles in order under its role, as a role
chain (shi_ontology::chains_from, shi_ontology::chain_roles): an interpretation
satisfies the chains of a closure exactly when it satisfies those axioms
(ChainsHold, chains_from_correct), since a chain of the Direct Semantics relates
along its roles as `Along` does (chainRelation_along). The class parts leave
the axioms to the chains, their roles must not be built in (RoleProper,
shi_ontology::chain_proper), and every closure with chains goes to the
completion forest (shi_ontology::chained), which `role_chains::satisfiable` now
always calls, so a closure without chains is decided as before. The acceptances
come with an OWL model that satisfies the chains (owl_model_chain_axiom), and
every OWL model of the closure satisfies them, so the rejections stay exact
(prepared_sound, prepared_complete); the answers also come from Functional
Syntax source bytes.

The encoding now refuses to nest an automaton into itself along the fillers of
its atoms (role_chains::nests, nests_total), which only a hierarchy that is not
regular calls for, such as `r ∘ r⁻ ⊑ r`; such a closure gets no answer at once
instead of growing the table to its bound. This completes the stage: role
chains are decided with proofs, and of SROIQ only the universal and empty roles
(owl:topObjectProperty, owl:bottomObjectProperty) remain, besides datatypes
for OWL 2 DL. The tests decide uncle chains between individuals, chains through
class inclusions and their inverses, left recursive chains such as
`locatedIn ∘ partOf ⊑ locatedIn`, and every one of 200 random classes over two
chains, all with a model of at most three elements coming out satisfiable.

This block adds 6 public theorems and 2 independent definitions. Totals are
1648 audited theorems, 906 definitions, 456 Rust regressions and 1841 ledger
obligations.

## Reasoner: the empty role

The sixteenth stage adds the universal and empty roles of SROIQ,
`owl:topObjectProperty` and `owl:bottomObjectProperty`, whose fixed meanings,
every pair and no pair, the tableaux do not model by themselves. Its first
block decides the empty role.

The tableaux read `owl:bottomObjectProperty` as an ordinary role, and the
preparation conjoins `∀B.⊥` onto the TBox concept (withEmpty,
shi_ontology::empty_role, empty_role_correct), so in every model of the
tableaux it relates nothing, as in every OWL interpretation
(with_empty_axioms). The OWL model built from a tableau's model then relates
along every role other than the universal one as the tableau's model does
(owl_model_relation), the empty role included, so concepts, inclusions,
chains, characteristics and assertions with the empty role keep their meaning,
and every OWL model satisfies the extra conjunct, so the rejections stay exact.
The properness checks now exclude only `owl:topObjectProperty`
(shi_ontology::not_top, not_top_correct): a role included in the empty role
relates nothing, a chain into it forbids its paths, an assertion along it
contradicts the closure, and the empty role is irreflexive, asymmetric,
functional and disjoint from every role but not reflexive. The tests decide
these from axioms and from Functional Syntax source bytes.

This block adds 4 public theorems. Totals are 1652 audited theorems, 906
definitions, 458 Rust regressions and 1845 ledger obligations.

## Reasoner: the universal role

The universal role `owl:topObjectProperty` relates every pair, which no model
of the tableaux has to. A restriction along it, `∃U.C` or `∀U.C` in either
orientation, therefore holds at every element or at none (Global,
global_denote): its truth is one global choice (GlobalTruth). A question that
uses the universal role goes to the completion forest through a case split
(universal::satisfiable, Rowl.Universal.satisfiable_correct), which leaves the
forest, the role chains and their proofs untouched.

The restrictions along the universal role are collected once each, the atoms,
with every atom of their fillers (universal::collect, collect_correct). Under a
guess for their truths every atom becomes `⊤` or `⊥`, `∃U.Self` becomes `⊤`
and its complement `⊥` (fixedOf, fixed_correct), and the guess is made good by
what it requires (Required, require_correct): a further element at a further
node in the filler of a true `∃U.C` or outside the filler of a false `∀U.C`,
and the filler of a true `∀U.C` or the complement of the filler of a false
`∃U.C` in the TBox concept. The forest decides each guess (guessed_correct) and
the search tries them in turn, accepting with the first guess that has a model
(guesses_correct). In a model of a guess's requirements, every guess is the
truth of its atom once the universal role relates every pair, the atoms of a
filler first (requirements_exact), so the concepts under the guess mean the
concepts (fixed_meaning); and a model of the question in which the universal
role relates every pair is a model of the guess of its own truths, with its
witnesses at the further nodes. No name has to be fresh. An earlier encoding
through a hub, an individual every element relates to along `U`, was exact
too, but per-node choices about global restrictions all passed through the hub
and made the forest's backjumping thrash on small inputs; the case split takes
those choices once.

The ontology queries now take the universal role in every concept except
number restrictions, which OWL 2 DL forbids along it (Proper, NoTopCount), and
in inclusions and chains into it, its symmetry and transitivity, and
assertions along it, which hold for every pair; it may not be included in
another role, inverse or equivalent to one, asymmetric or disjoint from one
(RoleProper). An acceptance comes with an OWL model built from the forest's
model with the universal role then relating every pair (withUniversal), which
keeps every role axiom of the closure (universal_role_axiom,
universal_constraint_axiom, universal_chain_axiom); negative assertions along
the universal role refute the closure through their refusals. This completes
SROIQ: with datatypes, full OWL 2 DL remains. The tests decide global
existence and universality, domains and ranges of the universal role, a
prescription that needs review everywhere once any patient takes warfarin,
also from Functional Syntax source bytes, and every one of 200 random concepts
over the universal role, all with a model of at most three elements coming
out satisfiable, in under a second.

This block adds 36 public theorems and 9 independent definitions. Totals are
1688 audited theorems, 915 definitions, 463 Rust regressions and 1881 ledger
obligations.
