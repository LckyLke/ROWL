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
blank-isomorphism proofs. Canonical blank scopes across imports, the completeness
of the RDF-to-OWL mapping, the writing direction of the OWL 2012/RDF 1.1 literal
bridge and the other required serializations remain separate M3 obligations. Full M3 and M4 completion claims are unchanged.


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

## M5: the values of five datatypes

`Rowl.DatatypeMap` specifies the OWL 2 datatype map on five datatypes,
independently of the kernel: `xsd:integer`, `xsd:decimal`, `xsd:string`,
`rdf:PlainLiteral` and `xsd:boolean`. A datatype map is normative on them
(Normative) when it supports them with the XML Schema 1.1 lexical spaces
(integer and decimal numerals with an optional sign, IntegerForm and
DecimalForm; strings of XML characters, XmlText; `text@tag` with an empty or a
well-formed BCP 47 tag after the last `@`, PlainSplit and LanguageTag; `true`,
`false`, `1` and `0`, TruthForm), their lexical-to-value mappings and their
value spaces: numbers are the images of rationals, the integers and the decimal
numbers among them, strings and strings with a lower-case tag the images of
their bytes, and truth values the images of the Booleans, injectively, with
numbers, plain literals and truth values pairwise different. Every other
datatype and the facets stay open. A model map satisfies the specification
(modelMap, modelNormative), so it is not contradictory; building it needed the
fact that no well-formed language tag is empty (well_formed_nonempty), without
which the untagged and tagged plain literal values would have to coincide.

The actual kernel function `datatypes::literal_value` returns a value exactly
for a literal of one of the five datatypes whose lexical form is in the lexical
space (literal_value_correct, kind_value_correct). A number is kept canonical,
as its sign, the digits of its integer part without leading zeros and the
digits of its fraction without trailing zeros (number_value_correct,
CanonicalNumber), so that two canonical numbers write the same rational exactly
when they are equal (numberOf_injective): `1`, `+01` and `1.000` are one value.
A plain literal splits at its last `@` (plain_split_unique) and lowers its tag;
a string is its bytes. Under every normative map the literal is then in the
lexical space with that value, distinct canonical values are distinct values
(value_injective, same_value_correct), and the kernel's datatype membership is
membership in the value space (in_kind_correct, normative_in_kind): integers are
decimals, strings are plain literals, and nothing else overlaps. These values
are what the reasoner needs to tell literals apart and to place them in data
ranges.

This block adds 66 public theorems and 41 independent definitions. Totals are
1754 audited theorems, 956 definitions, 469 Rust regressions and 1947 ledger
obligations.

## M5: data properties and literals in the ontology queries

`data_ontology` answers consistency, class satisfiability, subsumption and
instance checking for closures with data properties and literals of the five
datatypes, by an encoding into classes, object properties and named
individuals that the SROIQ queries of `shi_ontology` decide. The data values of
a model become further elements, the data nodes, of a class `D`; every data
property of the context (`Context`: the distinct literal values, the kinds in
use, the object and the data properties) becomes an object property from
elements that are no data nodes to data nodes, `owl:bottomDataProperty` the
empty role; every literal value becomes a named data node, in the kind classes
its value is in and with a pattern of bit classes that tells it apart; every
datatype in use becomes a class, with the inclusions of integers in decimals and
of strings in plain literals, the disjointness of the rest, and the booleans as
the two truth values; and every object property of the context relates only
elements that are no data nodes (`encode_meaning`, `Frame`). A class expression
that a data node could satisfy is conjoined with the complement of `D` on the
left of an inclusion, in equivalent and disjoint classes and in assertions;
guarded expressions (named classes other than `owl:Thing`, nominals and
restrictions that need a neighbour) are not, since no data node of a model made
from an OWL model satisfies them (`guarded_meaning`).

A correspondence between an OWL interpretation and an interpretation of the
encoding (`Simulates`) places the elements of the first one to one at the
elements of the second that are no data nodes, agrees on every name that is not
the encoding's, and counts the values of every data restriction alike; under it
the encoding of a class expression holds exactly where the expression does
(`encode_class_meaning`, `encode_range_meaning`). For axioms the values of the
data properties also sit at data nodes one to one, element by element
(`Placed`), and each of the 37 axiom forms is satisfied exactly when the axioms
it becomes are (`encode_axiom_meaning`); the converse direction needs the data
nodes kept apart from the names (`Inert`). An OWL model gives such a
correspondence with its own values as the data nodes (`lifted`,
`lifted_satisfies`, `lifted_class`). A model of the encoding gives one too
(`sound`, `sound_satisfies`, `sound_class`): its elements that are no data nodes
are the OWL elements, each literal value's individual gets its value, and each
element gives each data node that witnesses one of its finitely many data
restrictions a fresh value of the kinds that node's classes say. The values
come from infinite regions of integers, decimals that are no integers, strings
of the letter a, tagged strings and values outside every datatype
(`regionValue`, `region_space`, `region_profile`), beyond the finitely many
literal values, so distinct nodes of an element get distinct values. The truth
values are the only booleans, so a boolean data node is always a literal's.
Reinterpreting anonymous individuals leaves the encoded fillers' meaning
unchanged (`filler_anonymous`). Under every datatype map that is the OWL 2 map
on the five datatypes, an answer of the queries is therefore the answer of the
2012 Direct Semantics (`consistent_correct`, `class_satisfiable_correct`,
`subsumed_correct`, `instance_of_correct`, and their prepared forms on a closure
prepared once, `prepare_correct`).

There is no answer for a datatype restriction, a datatype definition, a key,
another datatype, a literal outside its lexical space, `owl:topDataProperty`
outside an inclusion into it, `owl:Thing` as a disjoint union, a number
restriction along the universal role, the universal role included in another
role, in a chain included in another role, equivalent or inverse to a role, or
functional or inverse functional, a name starting with the byte 0, or a
question that names an anonymous individual or one that the closure does not
name. Closures without data properties, literal values and datatypes go to the
SROIQ queries unchanged. The Functional Syntax reader does not read data
axioms yet, and facets remain pending.

This block adds 340 public theorems and 78 definitions. Totals are 2094
audited theorems, 1034 definitions, 481 Rust regressions and 2287 ledger
obligations.

## M3: self and number restrictions in Functional Syntax

The class-expression reader (`functional_classes`) now reads `ObjectHasSelf`
and `ObjectMinCardinality`, `ObjectMaxCardinality` and `ObjectExactCardinality`
with or without a filler, so documents use every object class expression that
the ontology queries decide. A number restriction reads, after its `(`, an
integer token, an object property expression, the optional filler (none before
`)` or at the end, `read_filler`) and `)`. The number's ASCII digits are read
by the bounded decimal reader `decimal::read_bounded`: it returns the value as a
machine integer exactly when the span is a nonempty run of digits inside the
bytes whose value is at most the count limit (`Rowl.Decimal.Bounded`,
`read_bounded_total_correct`, `read_bounded_some_iff`, `read_bounded_none_iff`),
and it stops as soon as a prefix exceeds the limit, so a number such as a
thousand nines is rejected at its token without forming its value; the earlier
`read_span` would build the unary natural of any number. The count limit thus
bounds the members of each intersection, union and enumeration and the value of
each number restriction, and a larger number is the count-limit error at the
number, before the property is read.

The independent grammar gains the self and number restriction bodies and the
optional filler (`FillerRun`), in the same mutual derivation as class
expressions, connective bodies and member sequences, with both directions
proved (`read_filler_total_correct`, `filler_execution`). The mapping into the
model turns a self restriction into `ObjectHasSelf` and a number restriction
into the restriction of its bound with the number as a unary natural
(`NaturalOf`, `natural_correct`, `natural_of_value`, `CardinalityOf`) and the
model of its filler; every accepted expression is still shaped, so every read
document maps (`filler_run_shaped`). The source queries answer from the bytes
of documents with number and self restrictions. The six data restrictions are
still reported as unsupported.

This block adds 9 public theorems and 4 definitions. Totals are 2103 audited
theorems, 1038 definitions, 485 Rust regressions and 2296 ledger obligations.

## M3: data ranges and data restrictions in Functional Syntax

A new reader (`functional_ranges`) reads one data range at a caller-supplied
position: a datatype IRI, `DataIntersectionOf` and `DataUnionOf` with at least
two members, `DataComplementOf`, `DataOneOf` with at least one literal, and
`DatatypeRestriction` with a datatype IRI and at least one pair of a facet IRI
and a literal. `read_optional_range` reads the optional data range of a data
number restriction. Literals use the proved literal reader. The independent
grammar (`RangeRun`, `BodyRun`, `MembersRun`, with `LiteralsRun`, `FacetsRun`
and `OptionalRun`) is proved equivalent to the actual reader in both directions,
with the first error in source order and progress on success.

The class-expression reader now reads the six data restrictions, so all
eighteen class-expression forms are read: `DataSomeValuesFrom` and
`DataAllValuesFrom` with one data property and a data range, `DataHasValue` with
one data property and a literal, and `DataMinCardinality`,
`DataMaxCardinality` and `DataExactCardinality` with a number (the bounded
reading of the previous stage), one data property and an optional data range
(`DataPropertyRun` and the new connective derivations). The model mapping turns
data ranges into the model's data ranges with exact IRIs and literals and the
facets in order (`RangeModel`, `FacetOf`, `data_range_correct`) and data
restrictions into the model's data restrictions (`DataCardinalityOf`); every
accepted data range is shaped (`RangeShaped`, `range_run_shaped`), so every read
document still maps.

The ontology queries take data restrictions over the five datatypes since the
data encoding stage; documents with data property axioms are read by the next
stage, and datatype restrictions are read but not yet reasoned about.

This block adds 39 public theorems and 18 definitions. Totals are 2142 audited
theorems, 1056 definitions, 491 Rust regressions and 2335 ledger obligations.

## M3: data property axioms, keys and data assertions in Functional Syntax

A new reader (`functional_data_axioms`) reads `SubDataPropertyOf`,
`EquivalentDataProperties` and `DisjointDataProperties` with at least two data
properties, `DataPropertyDomain` with a class expression, `DataPropertyRange`
with a data range, `FunctionalDataProperty`, `DatatypeDefinition` with a
datatype and a data range, and `HasKey` with a class expression and two
parenthesized, possibly empty lists of object and data properties, each with its
axiom annotations. Data properties and datatypes are IRIs (`IriRun`), property
lists share the count limit (`IrisRun`, `ObjectsRun`, `ListRun`), and class
expressions and data ranges use the proved readers (`ClassStep`, `RangeStep`).
The independent grammar (`BodyRun`, `AxiomRun`) is proved equivalent to the
reader in both directions, with the first error in source order and progress
(`data_axiom_progress`).

The assertion reader adds `DataPropertyAssertion` and
`NegativeDataPropertyAssertion` with a data property, an individual and a
literal (`DataEdgeRun`). The document reader dispatches the eight data axiom
keywords to the new reader and the data assertions to the assertion reader, so
all 37 axiom forms are read and no axiom is reported as unsupported any more
(`AxiomStep` loses its offset). The model mapping turns the data axioms and
assertions into the model's (`DataAxiomModel`, `DataMembersModel`,
`data_axiom_correct`), and every accepted data axiom is shaped (`ShapedData`), so
every read document maps.

This block adds 40 public theorems and 17 definitions. Totals are 2182 audited
theorems, 1073 definitions, 494 Rust regressions and 2375 ledger obligations.

## M6: answers about data from Functional Syntax bytes

The source queries (`source_reasoning`) now run the data queries of
`data_ontology` instead of the SROIQ queries alone, so a Functional Syntax
document with data property axioms, data restrictions and data property
assertions is answered from its original bytes in one extracted unit, and
`source_prepared` prepares a document once for the prepared data queries. A
closure without data properties, literal values and datatypes still goes to the
SROIQ queries unchanged. The source theorems (`source_consistent_correct` and
the others) now state each answer under every datatype map that is the OWL 2 map
on the five datatypes (`Normative`), in the universes of the data queries, and
`source_prepared_correct` describes a prepared closure by `DataPrepared`; the
completeness and soundness corollaries hold in the same universes.

## Performance: linear lexing on validated text

The lexer validates the whole source before selecting tokens, so it now selects
each token with matchers that use that fact. `longest::longest_valid_prefix`
stops as soon as the derivative is the empty expression (`dead_total_correct`),
because no longer prefix can then match, and on any suffix with a UTF-8
decoding it returns exactly what `longest_prefix` returns
(`longest_valid_prefix_eq`). `functional::next_terminal_fast` decodes the next
code point and runs only the matchers of terminals whose words can begin with it
(`may_start`). `FunctionalFast.lean` proves the test sound against the
independent terminal languages (`may_start_sound`): a skipped terminal has no
candidate endpoint (`longest_skip`), so skipping it leaves the selection
unchanged, and on a valid suffix `next_terminal_fast_eq` equates the dispatching
selection with the standard greatest selection `next_terminal`. The stream
proofs in `FunctionalLexer.lean` rewrite with these equalities, so every lexer
theorem keeps its statement.

Each token scan now ends where its longest possible match ends instead of at the
end of the document, and most terminals are not tried at all. On a generated
200-class document lexing went from 1.55 s to 0.23 s in a release build. The
remaining reader cost is IRI validation, which derives the RFC 3987 grammar
code point by code point.

This block adds 13 public theorems. Totals are 2195 audited theorems, 1073
definitions, 497 Rust regressions and 2388 ledger obligations.

## Performance: compiled grammars for IRI validation

Validating an IRI derived the RFC 3987 grammar code point by code point, and
each derivative step copied whatever followed a nullable part, which for this
grammar is most of it: about 2 ms per IRI. The new kernel module `compiled`
compiles an expression into a node table whose parts precede their nodes and
matches by partial derivatives over continuation stacks of node indices, with
equal stacks merged, so no part of the grammar is copied while matching.

`Compiled.lean` gives the table an independent reading (`lang`, with
`stackLang` and `stateLang` for stacks and states) and proves that compiling
keeps every empty-word flag right and gives the root the expression's language
(`compile_spec`), that each step replaces the state's language by its left
quotient by the code point (`derive_spec`, `derive_stack_spec`, `step_spec`),
and, by running in lockstep with the derivative matcher, that `matches` returns
exactly `matches_utf8`'s result (`matches_eq`) and `longest_valid` exactly
`longest_prefix`'s result on a suffix with a UTF-8 decoding
(`longest_valid_eq`). `iri::validate_iri` and `validate_reference` now match
through a compiled table and fall back to the derivative matcher only when a
vector would exceed the `usize` range; `Iri.lean` proves them equal to the
derivative matcher, so every IRI theorem keeps its statement. Reading a
generated 400-class document now takes 1.1 s instead of 5.0 s.

This block adds 47 public theorems and 8 definitions. Totals are 2242 audited
theorems, 1081 definitions, 501 Rust regressions and 2435 ledger obligations.

## Performance: a concept table prepared once per ontology

Every query of the completion graph tableau interned the whole TBox, the facts
and the definitions into a fresh concept table, with a linear lookup per entry,
so the setup of one query grew quadratically with the ontology: 3.7 ms on a
generated 400-class ontology. `completion::base` now interns them and closes
the table once; `shi_ontology::prepare` stores the result in the prepared
closure. `completion::satisfiable_from` copies the base's table, interns only
the query's facts, closes the copy again and runs the tableau.
`Completion.lean` proves the copies exact (`copy_entries_correct`,
`copy_requirements_correct`, `copy_unfoldings_correct`), describes a base by
`BaseFor` (`base_correct`) and proves `satisfiable_from` correct with exactly
the conclusions of `satisfiable_correct` on the base's facts, TBox concept and
definitions (`satisfiable_from_correct`). `ShiOntology.lean` routes the
tableau's answer through `TableauRun`, which uses the base when preparation
produced one, so every prepared query keeps its theorem. The per-query setup
on the 400-class ontology is now 0.2 ms; the tableau run itself, which rescans
every unfolding at every node, is now the main cost.

This block adds 6 public theorems and 2 definitions. Totals are 2248 audited
theorems, 1083 definitions, 502 Rust regressions and 2441 ledger obligations.

## Performance: unfoldings indexed by their trigger

With the table prepared once, the tableau run dominated, and in it the check of
a node: it walked every unfolding of the ontology and, for each, compared IRI
spellings against the node's label, about 40 µs per node on the 400-class
ontology. A problem now lists, for every entry of its concept table, the
unfoldings whose class the entry is (`triggers`, built by `triggers_from` once
for a base and extended only for a query's new entries), and
`missing_unfolding` walks the label's items and only their unfoldings. The
unused per-unfolding check and `has_atom` are gone. `CompletionSearch.lean`
states the index (`TriggersFor`, `TriggersOk`) and proves the new search with
the same conclusions as before (`missing_unfolding_correct`); the index is a
fixed hypothesis of the rule searches and of `run_correct` for both tableaux,
and `Completion.lean` proves it for every problem that `satisfiable`, `base`,
`satisfiable_from` and the completion forest build (`triggered_by_correct`,
`triggers_from_correct`, `triggers_fresh`). The slowest queries on the
400-class ontology went from about 450 ms to about 3.5 ms, and the average
query from 23 ms to 2.3 ms.

This block adds 4 public theorems and 2 definitions and removes
`has_atom_correct`. Totals are 2251 audited theorems, 1085 definitions, 502
Rust regressions and 2444 ledger obligations.

## Reasoner: verified classification

Classifying the named classes asked one subsumption question per ordered pair
of classes, about 190 000 tableau runs for a generated 437-class ontology. The
new kernel module `classification` answers the satisfiability of every listed
class and the subsumption of every pair from far fewer runs. `told` reads the
told parents of every class from the subclass axioms whose left side is the
class and whose right side names a class or an intersection with named
members, from the equivalences that list the class next to such expressions
and from the disjoint unions that list it. The classes are ordered by their
depth in this told hierarchy, and each class's row is filled along that order:
the class itself and its told parents are above it, a class without instances
is above no satisfiable class, a class with a told parent that the row already
refuses is not above it, a class above an already classified told parent is
above it, and only the remaining pairs go to the prepared subsumption query. A
class without instances is below every class. A final pass over all classes
makes the rows complete whatever the order, so the order only decides how many
questions are saved.

`Classification.lean` defines what one axiom tells about two named classes
(`Told`) and proves every told pair subsumed in every model of the closure
(`told_subsumed`), proves the told parents listed by `told` right
(`told_spec`, with `ParentsOk`), proves each answer of a row right from the
prepared queries' theorems, the meaning of subsumption (reflexivity,
transitivity, classes without instances) and earlier right rows (`decide_spec`,
with `Right`, `RowRight` and `Context`), and proves the loops complete. Its
main theorem, `classify_correct`, states that whenever `classify` answers, it
lists for every listed class exactly whether it is satisfiable and for every
pair exactly whether the first is subsumed by the second, under every normative
datatype map and vocabulary. `Reasoner::classify` and the CLI's `classify`
command now use it, and a new regression compares its answers with the
pairwise queries on random ontologies and on the examples. On the 437-class
ontology it asks 11 450 questions and classifies in about 27 s in a release
build.

This block adds 50 public theorems and 10 definitions. Totals are 2301 audited
theorems, 1095 definitions, 506 Rust regressions and 2494 ledger obligations.

## Performance: group tests for classification

The verified classification still asked one subsumption question for every pair
that the told hierarchy and earlier answers left open: 11 450 questions for the
437-class ontology, almost all of them refuted. The open pairs are now tested in
groups. `escapes` asks one prepared satisfiability query: whether the class has
an instance outside every class of a group, built as the intersection of the
class with the complements of the group (`complements`). When it has, every
class of the group is refuted at once; otherwise `split` halves the group, and a
single class that the class cannot escape subsumes it. `rounds` repeats a cheap
pass (`fill` with `settle`, which applies only the rules that need no query) and
a group test of the open classes whose told parents all subsume the class
(`candidates`), so the told children of every refuted class are refuted by the
next pass without a query; a final test takes every class still open, which
keeps each row complete.

`Classification.lean` proves the group test exact in both directions: an
instance outside the group refutes each of its classes (`escape_refutes`), and
no instance of a class outside a single class makes it a subsumer
(`no_escape_subsumes`); `escapes_spec` lifts both to the prepared query's
theorem. `mark_spec` and `split_spec` prove that splitting answers every class
of the group with `yes` or `no`, keeps the row right and changes no other answer
except to `yes` or `no`; `candidates_spec` proves that the final group holds
every class still open, so `row_of_spec`, and with it `classify_correct`, keep
their statements. On the 437-class ontology classification runs 871
satisfiability queries instead of 11 450 subsumption queries, and `rowl
classify` takes 2.3 s instead of 13.4 s in a release build.

This block adds 9 public theorems and removes `ask_spec`, `decide_spec` and
`fill_rest_spec`. Totals are 2307 audited theorems, 1095 definitions, 506 Rust
regressions and 2500 ledger obligations.

## Python bindings

The `rowl` Python package in `bindings/python` reads an OWL Functional Syntax
document once and answers consistency, satisfiability, subsumption, instance
and classification questions by IRI, with `True`, `False` (not entailed) or
`None` (outside the supported fragment). It loads the C interface of the new
`rowl-python` crate with `ctypes`, so it needs no third-party Python or Rust
packages; `pip install --no-build-isolation ./bindings/python` builds the
library with cargo and ships it inside the package. The crate wraps
`rowl::reasoner::Reasoner` behind an opaque handle, takes text as UTF-8 bytes
with a length, returns lists as JSON text and adds no reasoning. It is the only
crate outside the kernel with `unsafe` code, confined to reading the caller's
buffers and releasing handles and text, and it does not take the workspace's
`unsafe_code = "forbid"` lint for that reason.

Two Rust tests drive the C interface on the medication-safety example and on
rejected documents and invalid arguments, and nine Python tests check the
package, including that its classification agrees with the pairwise questions.
Totals are 2307 audited theorems, 1095 definitions, 508 Rust regressions and
2500 ledger obligations.

## Performance: anywhere blocking in the completion graph

The completion graph blocked a tree node only when its own path to the named
root repeated a label, so equal labels in different branches were expanded
again and again: on a generated 1091-class ontology a single query built up to
600 nodes, and classifying it took 60 s. A tree node is now blocked when its
parent is, or when an earlier tree node that is not blocked has a label of the
same length with the same items (anywhere equality blocking, which inverse roles
need). `blocking` computes the flags of all nodes in one pass in index order
(`blocked_at`, `repeated_before`, `blocks`), and `missing_successor` reads them.

`CompletionSearch.lean` states the new condition (`Blocked`, with `FlagBlocks`
for the flags) and proves the flags exact (`blocks_correct`,
`repeated_before_correct`, `blocked_at_correct`, `blocking_correct`); the rule
search keeps its statement. The model of a complete graph needs nothing more: a
blocked child of an unblocked node has an unblocked tree node with its label,
whose label is an element of the model (`child_blocked`). Termination keeps its
measure: the old path condition is kept as `PathBlocked`, and a node blocked
along its path is blocked anywhere, because labels without repetitions that have
the same items have the same length (`path_blocked_blocked`), so an unblocked
node still has a path of distinct labels (`depth_le`). On the 1091-class
ontology the largest query graph has 67 nodes and classification takes 10 s.

This block adds 7 public theorems and 2 definitions and removes
`repeats_above_correct` and `blocked_correct`. Totals are 2312 audited
theorems, 1097 definitions, 508 Rust regressions and 2505 ledger obligations.

## M3: reading OWL ontologies from RDF graphs

`rdf_mapping::map_graph` reads an OWL ontology from a raw RDF graph by the
reverse of the OWL 2 mapping to RDF graphs (2012, §2.1-2.3, Tables 1-4). It
first takes the declarations (`rdf:type` triples on IRIs with a declaration
type), then the ontology header (the IRI typed `owl:Ontology`, its version IRI,
its imports and its annotations by declared annotation properties), and then
reads an axiom from each triple not yet read: the predicate selects the reader,
which reads the class expressions, data ranges, property expressions and RDF
lists the triple refers to and marks every triple it uses. A blank node of an
expression must be typed `owl:Class`, `owl:Restriction` or `rdfs:Datatype`;
triples about it wait until the axiom that refers to it reads them. The graph
must declare every class, datatype and property it uses, as OWL 2 DL requires,
and `owl:AllDisjointClasses`, `owl:AllDisjointProperties` and `owl:AllDifferent`
need three members or more, since two-member forms use the binary vocabulary.
The read fails when a triple is left unread, apart from exact repetitions of a
read triple, so a blank node shared by two expressions is refused.

`RdfMapping.lean` states the forward mapping independently of the Rust code, as
relations from structural objects, a supply of fresh blank nodes in allocation
order and a node to the triple patterns they produce (`TCE`, `TDR`, `TOPE`,
`TAxiom`, `THeader`, `TOntology`). Triples compare through views (`Matches`):
IRIs by spelling, blank nodes as they are, literals by lexical form and datatype
IRI or language tag. A structural `rdf:PlainLiteral` maps to the RDF 1.1
literal with the language tag after its last `@`, or to an `xsd:string` literal
when that tag is empty (`LiteralNode`), and a cardinality to its canonical
`xsd:nonNegativeInteger` spelling. Every reader is proved to use exactly the
triples of the forward mapping of what it returns and to allocate the blank
nodes of that mapping in order (`Grows`), the recursive readers by induction on
their fuel (`data_range_right`, `class_expression_right`). `map_graph_correct`
proves that whenever `map_graph` returns an ontology and its blank nodes, the
axioms and the header carry no annotations of their own and the forward mapping
of the ontology, allocating exactly those blank nodes, gives the input graph:
every triple instantiates a pattern and every pattern is instantiated by a
triple of the graph.

Not proved: that the forward mapping of every such ontology is read back,
annotated axioms and their reification, `owl:imports` closure, that the returned
blank nodes are distinct, and RDF datasets.

This block adds 126 public theorems and 36 definitions. Totals are 2438 audited
theorems, 1133 definitions, 511 Rust regressions and 2631 ledger obligations.

## Reading ontologies from N-Triples

`Reasoner::from_ntriples` reads an N-Triples document with the verified reader,
reads the OWL ontology its graph encodes with `rdf_mapping::map_graph` and
prepares the queries once, as `from_functional` does for Functional Syntax; a
graph the mapping does not read is reported apart from a syntax error. The
CLI's `check`, `classify` and `instances` commands read `.nt` files this way,
the C interface has `rowl_reasoner_from_ntriples`, and the Python
`Reasoner.from_file` reads N-Triples for a `.nt` file. The medication example
in N-Triples gives the same classes, individuals, classification and instance
answers as its Functional Syntax version. The layer adds no reasoning: the
answers are those of the verified queries for the ontology the mapping returns,
and `map_graph_correct` relates that ontology to the graph.

The verified readers, the mapping and the queries recurse over the length of
their input, so a generated 5000-class ontology overflowed the default stack
in either syntax. `Reasoner` now runs every kernel call on a thread with a
1 GiB stack, committed only as it is used; the answers are unchanged. Totals are
513 Rust regressions and 11 Python binding tests.

## Reasoner: classifying EL ontologies by saturation

The tableau classification asks satisfiability questions, so on large EL
ontologies, the common case for terminologies, it spends most of its time
building completion graphs for subsumptions that follow from a few told
axioms. `saturation::classify` classifies an ontology whose logical axioms are
EL by saturation instead. Every class expression of the axioms is interned
into a table of concepts, hashed into buckets, whose parts come before them:
the top and bottom concepts, atoms, binary conjunctions and existential
restrictions on named object properties. The axioms become rules over the
table: concept inclusions (from subclass axioms, consecutive members of
equivalence axioms both ways, conjunctions of two members of a disjointness
axiom below the bottom concept and existential restrictions of a domain),
role inclusions (from subproperty axioms and two-member equivalences) and
chains of two roles (from chains and transitivity). The left-hand sides are
registered in indexes, together with their parts, so that a concept that
completes a conjunction or an existential restriction finds it.

Saturation starts from a context for `owl:Thing` and for every listed class and
derives subsumers `x ⊑ c` and links `x r y` (every instance of `x` has an
`r`-successor in `y`) from a queue: the parts of a conjunction, the link of an
existential restriction, told subsumers, conjunctions whose other part is
present, existential restrictions back along the links into a context,
`owl:Nothing` back along links, the inclusions and chains of a link's role,
and a new context for the target of a link. A final pass checks that the
result is closed under every rule. A class is unsatisfiable when `owl:Nothing`
is among its subsumers or among those of `owl:Thing`, and otherwise subsumed
exactly by the classes among its subsumers.

`Saturation.lean` proves the translation exact: for every interpretation that
fixes `owl:Thing` and `owl:Nothing`, the axioms hold exactly when the rules do,
the meaning of a concept being stable as the table grows (`translate_spec`,
`concept_of_spec`). The indexes hold exactly the rules (`index_from_spec`,
`register_spec`). Every subsumer, link and queued fact the saturation derives
holds in every model of the rules (`saturate_spec`). An accepting final check
(`closed_spec`) gives the closure conditions, from which the active contexts
without `owl:Nothing` form a canonical model: a context is in the atoms among
its subsumers and linked along the roles of its links. Every context satisfies
its subsumers (`positive`), every registered concept, and every class concept,
that holds at a context is one of its subsumers (`negative`), so the canonical
model satisfies every rule (`canonical_models`) and, lifted with the built-in
names, every axiom. `classify_correct` proves that whenever classification
answers, each answer is the Direct Semantics answer under every vocabulary and
datatype map: a derived subsumer holds in every model, and a missing one has
the canonical model as a counter-model.

`Reasoner::classify` uses the saturation whenever it answers and the tableau
classification otherwise. On generated EL ontologies classification takes
1.9 s instead of 19.5 s for 1000 classes with the same answers, 9.8 s for 5000
classes and 47 s for 20 000 classes, where reading the document now takes
about 80% of the time. A regression test compares the two classifications on
400 random EL ontologies with unsatisfiable classes, chains and transitivity.

This block adds 139 public theorems and 35 definitions. Totals are 2577 audited
theorems, 1168 definitions, 515 Rust regressions and 2770 ledger obligations.

## Performance: plain IRIs without the grammar

After the saturation stage, reading took about 80% of the time on large EL
ontologies, and `iri::validate_iri` took most of it: every call built the RFC
3987 grammar, whose IPv6 alternatives make it large, compiled it into a node
table and dropped both again, about 220 µs per IRI. N-Triples readers call it
for every IRI and Functional Syntax prefix expansion for every abbreviated IRI.

`validate_iri` now first scans the bytes for the plain form
`scheme://host/segment…#fragment`, whose host, segments and fragment have only
ASCII letters, digits, `-`, `.`, `_` and `~` (and the fragment also `/`), and
accepts them without building the grammar; any other input goes to the compiled
grammar as before. `Iri.lean` proves that such bytes are ASCII, hence decode to
their own code points (`ascii_utf8`), and spell an IRI: the scheme, an
authority that is a registered name, a path of segments and an optional
fragment (`plain_iri_spec`). `validate_iri_total_correct` and
`validate_iri_accepted_iff` keep their statements. A regression test compares
the validator with the derivative matcher on random strings.

A plain IRI is now validated in about 40 ns. Reading a generated 5000-class
ontology in N-Triples takes 0.025 s instead of 10.8 s, and in Functional Syntax
3.3 s instead of 8.2 s, where lexing is now the main cost. Totals are 516 Rust
regressions; the audited theorems and definitions are unchanged.

## Reasoner: EL consistency, taxonomies and lazy preparation

With reading fast, a generated EL ontology with 20 000 classes still took 15 s
to classify from N-Triples: 60% of the time went into preparing the tableau
queries, which the saturation never uses but the CLI's consistency check did,
and 20% into the answer matrix of 400 million pairs.

`saturation::consistent` decides consistency of an EL ontology: the axioms have
a model exactly when `owl:Nothing` does not subsume `owl:Thing`.
`saturation::taxonomy` gives the classification as lists: for every listed class
whether it is satisfiable and, if so, the positions of the listed classes that
subsume it, found through a table from concepts to the positions of their
classes, so its size follows the subsumptions rather than the pairs. The proofs
in `Saturation.lean` now share one set of lemmas over what an accepted
saturation gives (`Saturated`): a listed class is satisfiable exactly when its
answer is not empty (`saturated_satisfiable_iff`), a satisfiable class is
subsumed by a class exactly when the class's concept is among its subsumers
(`saturated_subsumed_iff`), an unsatisfiable class by every class
(`saturated_empty_subsumed`), and the axioms have a model exactly when
`owl:Nothing` does not subsume `owl:Thing` (`saturated_consistent_iff`), the last
with the lifted canonical model rooted at `owl:Thing`. `classify_correct`,
`taxonomy_correct` and `consistent_correct` follow from them.

`Reasoner::consistent` and `Reasoner::classify` try the saturation first and the
tableau otherwise, and the reasoner prepares the tableau queries only when the
first question that needs them is asked; an ontology whose axioms the queries
cannot prepare now loads and answers what the saturation answers. The 20 000
class ontology classifies in 2.2 s from N-Triples, using 210 MB instead of
672 MB, and in 12 s from Functional Syntax. The regression test also compares
the taxonomy and the consistency answers with the tableau's on the 400 random
EL ontologies.

This block adds 13 public theorems and 3 definitions. Totals are 2590 audited
theorems, 1171 definitions, 516 Rust regressions and 2783 ledger obligations.

## Performance: a tighter start test for prefixed names

On the generated EL ontologies lexing was most of the time of reading
Functional Syntax. The first-code-point dispatch `functional::may_start` let the
prefix-name and abbreviated-IRI terminals through for every code point, so every
token, parentheses and whitespace included, built both name grammars, large
alternations of Unicode ranges, and derived them code point by code point.

`may_start` now admits the two terminals only for `:`, the ASCII letters and the
code points outside ASCII (`functional::name_start`). Every word of PNAME_NS
begins with `:` or a PN_CHARS_BASE code point, whose ASCII members are the
letters, and every word of PNAME_LN begins with a word of PNAME_NS.
`FunctionalFast.lean` proves this from the independent languages
(`prefix_start`), so `may_start_sound` holds for the two terminals as for the
others; `longest_skip` and `next_terminal_fast_eq` keep their statements, and so
does every lexer theorem. The dispatch regression test now also covers names
that begin with letters outside ASCII, digits, `_`, `-` and `.`.

Classifying the generated 20 000-class EL ontology from Functional Syntax takes
11.1 s instead of 13.7 s and the 5000-class one 2.7 s instead of 3.3 s; lexing
the larger one takes 8.3 s instead of 10.9 s. Keywords and names still build
their grammars.

This block adds no public theorems or definitions. Totals are 2590 audited
theorems, 1171 definitions, 516 Rust regressions and 2783 ledger obligations.

## Performance: prefixed names scanned over ASCII bytes

After the tighter start test, every prefixed name and every keyword still built
both name grammars and derived them code point by code point.
`names::ascii_prefix` and `names::ascii_abbreviated` now find the longest
PNAME_NS and PNAME_LN at a position by reading bytes. A prefix name is the run
of label bytes from the position (ASCII letters, digits, `_`, `-` and `.`)
followed by a colon, where the run is empty or begins with a letter and does
not end with a dot; an abbreviated IRI continues after the colon with the run of
label bytes there, which must begin with a letter, `_` or a digit, up to its
last byte other than a dot. The scanners decline when a byte outside ASCII ends
a run, since such a byte may continue the name, and `functional::longest_valid`
then matches the grammar as before.

`Names.lean` now also proves the answers against its independent languages.
ASCII bytes decode to one code point each; every code point of a label or
local name is a PN_CHARS code point or a dot, whose ASCII members are exactly
the label bytes; and a prefix name has one colon, at its end. So every
candidate span reads the whole label run and then the colon after it, and for
PNAME_LN a prefix of the run after the colon. Whenever the scanners answer, the
answer is the greatest candidate endpoint, or no endpoint when there is no
candidate (`ascii_prefix_correct`, `ascii_abbreviated_correct`). With
`longest_matched_iff` this gives `longest_valid_eq` again, which the stream
proofs in `FunctionalLexer.lean` use, so every lexer theorem keeps its
statement. A regression test compares the scanners and `longest_valid` with the
grammar matcher at every position of 3000 random strings of ASCII name
characters, dots, colons, delimiters and characters outside ASCII.

Classifying the generated 20 000-class EL ontology from Functional Syntax takes
4.3 s instead of 11.1 s and the 5000-class one 0.9 s instead of 2.7 s, with the
same answers; lexing the larger one takes 0.9 s instead of 8.3 s. Of the 4.0 s
that reading it takes, the largest part is now the reader's own grammar
matching for every abbreviated IRI; keywords still derive their literal
grammars.

This block adds 2 public theorems and no definitions. Totals are 2592 audited
theorems, 1171 definitions, 518 Rust regressions and 2785 ledger obligations.

## Performance: whole names over ASCII bytes

After the ASCII scanners, a profile of reading the generated 20 000-class
ontology put about 40% of the samples in resolving abbreviated IRIs and about
20% in the lexer. Reading an abbreviated IRI recognizes its span as a PNAME_LN
token (`functional::recognize`) and checks its prefix and local parts
(`names::validate_prefix`, `names::validate_local`) before it expands and
validates the IRI, and each of the three built its grammar and derived it code
point by code point. They now accept a buffer that the ASCII scan from its start
reads whole (`names::whole`), and match the grammar as before otherwise;
`validate_abbreviated` does the same.

`Names.lean` proves that a span from the start that ends at the end of the bytes
decodes all of them, so when a scan whose answers are greatest candidate
endpoints reads the bytes whole, they are a well-encoded word of the language
(`whole_scan_accepted`, with `whole_total_correct` for the test).
`validate_prefix_total_correct`, `validate_local_total_correct`,
`validate_abbreviated_total_correct` and the three `accepted_iff` theorems keep
their statements, and so do `recognize_total_correct` and
`recognize_accepted_iff` in `Functional.lean`, which now states the scanners'
contract for every terminal (`ascii_name_correct`). A regression test compares
the three validators and `recognize` with the grammar matcher on 3000 random
buffers of name pieces, some with a malformed byte.

Classifying the generated 20 000-class EL ontology from Functional Syntax now
takes 1.1 s instead of 4.3 s, faster than from N-Triples (2.3 to 2.5 s), and the
5000-class one 0.3 s instead of 0.9 s, with the same answers; reading the larger
one takes about 1.0 s instead of 4.0 s. Over the three performance stages its
classification went from 13.7 s to 1.1 s. Keywords still derive their literal
grammars, and full IRIs (`<…>`) are still matched by the RFC 3987 grammar both in
the lexer and in the reader.

This block adds 3 public theorems and no definitions. Totals are 2595 audited
theorems, 1171 definitions, 519 Rust regressions and 2788 ledger obligations.

## M4: OWL 2 DL validity of an axiom closure

`dl_validity::check_ontology` decides whether the supplied ontology, whose
axioms are taken as its complete axiom closure, satisfies the OWL 2 DL
restrictions that the verified checkers cover, and otherwise returns the first
violated one. It runs the checkers in the order of the condition lists of the
2012 Structural Specification, Section 3: nonempty keys (§9.5,
`keys::check_keys`) and the structural arities (`arity::check_arities`, with
the documented duplicate-disjointness decision); the
reserved vocabulary in the ontology and version IRIs (§3.1) and in every entity
position (§5.1–5.6, `vocabulary::check_reserved_vocabulary`); the typing
constraints with the built-in declarations of Table 5 (§5.8.1); and the global
restrictions of §11.2 in the order of that section: `owl:topDataProperty`
(`topdata::check_axioms`), datatypes with the positions of defined datatypes
(§9.4, `datatype_restrictions::check_structural_datatypes`), simple roles
(`roles::check_simplicity`), the property hierarchy (`role_order::check_regularity`)
and anonymous individuals (`anonymous_restrictions::check_anonymous`). A
violation names its restriction and carries the evidence of its component
checker: the offending axiom, the IRI and its kind, the role or the anonymous
individual.

The typing stage, `dl_validity::check_typing`, is new. `indexing::check_ontology_typing`
decides the same predicate on interned symbols, but its symbol table has a
capacity, so it can end without a verdict. `check_typing` compares exact IRI
spellings and always decides. It reads the declarations from the axioms in
order, reports the first declaration that conflicts with the built-in role of
its IRI or with a later declaration, and then the first use whose IRI is
neither built in nor declared with its kind; named individuals need no
declaration. Spellings are compared from the last byte, where the IRIs of one
namespace usually differ. Two shortcuts skip work that cannot fail: without a
property chain the empty order satisfies the restriction on the property
hierarchy, and without an object property assertion that has an anonymous
endpoint the anonymous individual graph has no edge, so only the positional
restriction on anonymous individuals is checked.

`DlValidity.lean` defines `OwlDlValid` as the conjunction of the components'
independent specifications: `Keys.ClosureOK`, `Arity.ClosureOK`,
`Vocabulary.VocabularyOK`, `Indexing.RawWellTyped`, `TopData.ClosureOK`,
`DatatypeRestrictions.StructuralRestriction`, `Roles.SimpleRestriction`,
`Roles.Regular` and `AnonymousRestrictions.Restriction`.
`check_ontology_total_correct` proves that `check_ontology` terminates and
returns `Valid` exactly for `OwlDlValid` ontologies, and otherwise a violation
whose `Correct` record holds its component's evidence (for example the first
forbidden axiom, the first conflicting declaration or a forced order pair that
the hierarchy contradicts), the proof that every earlier restriction holds and
the rejection of `OwlDlValid`. `check_ontology_valid_iff` is the acceptance
equivalence. `check_typing_total_correct` and `check_typing_valid_iff` prove the
typing stage exact against `RawWellTyped`, which `raw_well_typed_iff` rewrites
into conflict-free declarations (`ConflictFree`) and declared uses
(`Declared`); `check_typing_agrees` shows that whenever `check_ontology_typing`
completes, its verdict is the same. `no_chain_regular` and
`no_anonymous_assertion_restriction` justify the two shortcuts.

The umbrella requirements of the ledger were audited against the
specification text:

- `entity.EntityTyping` (§5.8.1) is `check_typing_valid_iff`.
- `entity.Punning` (§5.9): `typing_allows_punning` shows that the typing
  predicate forbids on one IRI only a class with a datatype and two different
  kinds of property, so every other reuse, such as one IRI as a class, an
  individual and an object property, is accepted. The Direct Semantics
  interprets these views by independent functions of the interpretation.
- `entity.DeclarationConsistency` (§5.8.2) is not an OWL 2 DL condition: an
  ontology may be used without consistent declarations. `check_declarations`
  decides it on its own (`check_declarations_valid_iff` against
  `ConsistentDeclarations`): every entity of the axioms, named individuals
  included, is declared with its kind, explicitly or by Table 5.
- `global.SimplePropertyClosure` is the existing `classify_non_simple_total_correct`:
  the set of non-simple object property expressions of the closure (§11.1),
  which `check_ontology` uses through `check_simplicity`.
- `global.BuiltinVocabularyRestrictions`: `builtin_vocabulary_restrictions`
  proves that every `OwlDlValid` ontology uses reserved IRIs only in their
  built-in roles and never as ontology or version IRI, uses
  `owl:topDataProperty` only as a SubDataPropertyOf superproperty, never puts
  `owl:topObjectProperty` or `owl:bottomObjectProperty` where a simple object
  property is required, and never redefines `rdfs:Literal` or a datatype of the
  OWL 2 datatype map. No further restriction on these positions exists in the
  2012 text; the literal and facet conditions on the built-in datatypes belong
  to the normative datatype map below. Following the literal text of §11.1,
  `ObjectInverseOf(owl:topObjectProperty)` is not composite.
- `global.AxiomClosureValidation` is `check_ontology_valid_iff`, with the
  exclusions below.
- `annotation.NoLogicalEffect`: `stripAnnotations` removes every axiom
  annotation, nested ones included, and every annotation axiom.
  `strip_annotations_satisfies` and `strip_annotations_models` prove that a
  closure and its stripped version have the same models, for every
  reinterpretation of the anonymous individuals, and
  `strip_annotations_model`, `strip_annotations_consistent` and
  `strip_annotations_entails` carry this to models with a vocabulary,
  consistency and entailment. Annotations still count for OWL 2 DL validity:
  annotation properties need declarations, and reserved IRIs, anonymous
  individuals and defined datatypes are restricted inside them.

Not checked: the lexical forms of literals in the lexical spaces of their
datatypes (§5.7) and facet values in the facet spaces of their datatypes
(§7.5), which need the normative datatype map (M5); and imports, since the
supplied axioms are taken as the complete closure, as for every component
checker. `OwlDlValid` therefore is the OWL 2 DL condition list of Section 3
without these two conditions and without the imported ontologies.

On the generated EL ontologies loaded from N-Triples, `check_ontology` takes
5.5 ms for 1000 classes, 0.10 s for 5000 classes and 3.4 s for 20 000 classes
(46 023 axioms), almost all in the typing stage, whose scans grow with the
square of the number of axioms. The anonymous restrictions alone took 3.6 s on
the largest ontology, which has no anonymous individual; the shortcut skips
them.

This block adds 21 public theorems and 16 definitions. Totals are 2616
audited theorems, 1187 definitions, 530 Rust regressions and 2809 ledger
obligations.

## Validating documents as OWL 2 DL

`Reasoner::dl_violation` runs the verified `dl_validity::check_ontology` on the
document's axioms when it is called and describes its verdict in words: `None`
when the axioms satisfy every restriction the check decides, and otherwise the
first violation, naming the restriction, the section of the Structural
Specification and the offending IRI with its kind, role, anonymous individual
or axiom with its position in the document. Loading never rejects a document
for these restrictions, so the queries still answer for documents that are not
OWL 2 DL. The CLI's `rowl validate FILE` prints `OWL 2 DL: valid` or
`OWL 2 DL: not valid:` followed by the violation and then exits with status 1;
it notes on standard error that imported ontologies are not read. The C
interface has `rowl_dl_violation`, which returns the violation as JSON text,
and the Python `Reasoner.dl_violation()` returns it as a string or `None`.
The layer only formats the kernel's verdict and adds no checking of its own.

Two examples were not OWL 2 DL: `maintenance-classes.ofn` used six classes
without declaring them, and `maintenance.nt` used three properties without
declaring them, so the reverse RDF mapping could not read it as an ontology.
Both now declare them; the reader and N-Triples tests count the added axioms
and triples. A test checks that every Functional Syntax and N-Triples example
is OWL 2 DL, and one crafted document per restriction checks the reported
violation through the reasoner, the CLI, the C interface and Python.

Totals are 537 Rust regressions and 13 Python binding tests; the audited
theorems, definitions and ledger obligations are unchanged.

## Hashed declaration lookups in the typing stage

The typing stage of `dl_validity::check_ontology` scanned every axiom for each
use and each declaration, so its time grew with the square of the number of
axioms. `check_typing` and `check_declarations` now first build a declaration
index: 4096 buckets, each holding, in increasing order, the positions of the
declaration axioms whose IRI hashes to it. The hash depends only on the bytes
of the IRI, so a declaration of a spelling can only sit in that spelling's
bucket. A use is declared when a declaration in its bucket has its spelling and
kind, and a declaration conflicts when a later declaration in its bucket has
its spelling and a forbidden kind. Spellings are still compared exactly; the
hash only selects the candidates, and colliding spellings stay apart.

The public theorems are unchanged and now prove the indexed implementation:
`check_typing_total_correct`, `check_typing_valid_iff`, `check_typing_agrees`,
`check_declarations_total_correct`, `check_declarations_valid_iff`,
`check_ontology_total_correct` and `check_ontology_valid_iff`. The index
invariant `IndexOK` says that the buckets are 4096, none is longer than the
number of axioms, and the position of every declaration axiom lies in the
bucket of its IRI. `declaration_index_spec` proves that the built index has
it, `declared_indexed_spec` that a bucket lookup finds a declaration of the
spelling and kind exactly when one of the axioms is such a declaration, and
`later_conflict_spec` that the bucket scan after a position finds a
conflicting kind exactly when a later declaration axiom has one. A new
regression declares two spellings that share a bucket.

On the generated EL ontologies loaded from N-Triples, `check_ontology` now
takes 5.3 ms for 1000 classes, 9.3 ms for 5000 classes and 38 ms for 20 000
classes (46 023 axioms), instead of 5.5 ms, 0.10 s and 3.4 s; the typing
stage alone takes 18 ms instead of 3.6 s on the largest one, and
`check_declarations` 16 ms instead of 2.0 s. The unchanged anonymous
restrictions took 4 ms on the largest ontology in this build and 4.9 s in the
previous one: their pairwise scans are quadratic in the number of axioms, and
whether the optimizer moves the test of the first axiom out of the inner scan
depends on the build. `check_ontology` does not depend on it, since its
shortcut skips those scans when no object property assertion has an anonymous
endpoint.

This block adds no public theorem or definition. Totals are 2616 audited
theorems, 1187 definitions, 538 Rust regressions and 2809 ledger obligations.

## Performance: indexed lookups in the RDF mapping

Reading a generated EL ontology with 20 000 classes from N-Triples spent 2.5 s
in `rdf_mapping::map_graph`, nearly all of it in lookups that scanned: `find`,
`find_type` and `find_any`, which look for an unused triple about a blank node,
went through every triple of the graph for each lookup, and `declared`, behind
`property_kind` and `node_kind`, went through every declaration for each
property it classified. Both made the mapping quadratic in the size of the
graph.

`map_graph` now builds two indexes once. The positions of the triples whose
subject is a blank node are bucketed by a hash of the node's scope and label in
ascending order (`subjects_from`), kept in the reader's `State`, and the
declarations are bucketed by a hash of their IRI (`Kinds`, filled by
`add_kind`). There is one bucket more than there are triples, at most 2^20. The
lookups go through the bucket of their node (`find_in`, `find_type_in`,
`find_any_in`) or IRI (`declared_in`) and check every candidate with the same
tests as before: unused, about the node, the predicate and the type. When the
bucket holds every triple of its node they therefore return the triple a scan
returned.

The lookup lemmas describe only what a lookup returns, so they hold whatever
the buckets contain. `fits_spec`, `fits_type_spec` and `fits_any_spec` prove
that an accepted candidate is an unused triple about the node with the
predicate (and type), `find_in_spec`, `find_type_in_spec` and `find_any_in_spec`
extend this to a bucket, and `find_spec`, `find_type_spec` and `find_any_spec`
keep their statements, now over the state. No lemma gives meaning to a lookup
that finds nothing, and the declaration lookups were never given one, so
`map_graph_correct` keeps its statement. That the buckets hold every triple of
their node, and so that the readers return what they returned before, is not
proved; the regression tests and the benchmark outputs show it.

On el20000.nt the mapping takes 0.063 s instead of 2.49 s and on el5000.nt
0.013 s instead of 0.142 s. On the same loaded machine `rowl classify` takes
0.76 s instead of 3.21 s on el20000.nt (2.2 s on an idle machine before) and
0.13 s instead of 0.32 s on el5000.nt, with the same output. A regression test
reads a graph of 1000 restrictions whose triples are far apart.

This block adds 6 public theorems and no definitions, and removes
`copy_kind_identity` with the function it described. Totals are 2621 audited
theorems, 1187 definitions, 539 Rust regressions and 2814 ledger obligations.

## M3: annotated axioms in the RDF mapping

`rdf_mapping::map_graph` read only axioms, headers and ontology annotations
without annotations of their own. It now reads them with their annotations, as
the OWL 2 mapping to RDF graphs writes them (§2.2, §2.3). An annotation whose
own annotations are not empty is reified by a blank node typed
`owl:Annotation`, with `owl:annotatedSource`, `owl:annotatedProperty` and
`owl:annotatedTarget` triples naming its triple, and that node carries the
annotations (Table 2). An axiom with annotations keeps its main triple, which a
blank node typed `owl:Axiom` reifies in the same way and which carries the
annotations (§2.3.1). The annotations of an axiom that a blank node represents,
an `owl:AllDisjointClasses`, `owl:AllDisjointProperties`, `owl:AllDifferent` or
`owl:NegativePropertyAssertion` node, are on that node (§2.3.3).

The reader first only collects which IRIs are declared with which kind; the
declaration triples are then read in graph order like the other axioms, so that
annotated declarations are read with their reifications. After reading an
axiom from its main triple it looks for an unused blank node of the right type
that reifies that triple, through a third index: the positions of the
`owl:annotatedSource` triples bucketed by a hash of their object (`reifier`). It
takes the four triples of the reification and every unused triple of its node
whose predicate is an annotation property, each with the annotations of its own
reification (`reified`, `node_annotations`); a reification without annotations
is refused. Axioms represented by a blank node read the annotations of that node
(`annotate`, `main_triples`). The main loop leaves the annotation triples of
reification nodes and of axiom nodes, which it recognizes by their types
(§3.1.2, Table 8), to the axiom that reads them, so the triples of a graph may
come in any order.

`RdfMapping.lean` states the forward mapping of annotations and annotated
axioms independently of the Rust code: `TAnn` and `TAnns` translate annotations
of a node (Table 2), `TReified` reifies main triples, `mainTriples` says how
many main triples the row of Table 1 of an axiom has (one, one per consecutive
pair of members for equivalences and equalities, §2.3.2, or none for axioms
represented by blank nodes), and `TAnnotatedAxiom` maps an axiom with its
annotations. `TAxiom` lists the main triples of each row of Table 1 first, as
the table writes them. `THeader` maps ontology annotations with theirs, and
`TOntology` allocates the blank nodes of the header before those of the axioms.
The readers' contract `ReadOk` now also says that the triples of an axiom start
with the pattern of the triple the reader started from (`matches_mk`), and
`declaration_spec` and `annotation_assertion_spec` cover the two new readers.
`reifier_spec` and `take_reifier` prove that a found reification is four unused
triples that reify the main triple, `annotations_right` proves the annotation
readers right by induction on their fuel, `main_triples_spec` relates the
reader's classification to `mainTriples`, and `annotate_spec` gives the
annotated axiom. `map_graph_correct` keeps its statement over the extended
relations: whenever `map_graph` returns an ontology and its blank nodes, the
forward mapping of that ontology, annotations included, allocating exactly
those blank nodes, gives the input graph.

The forward mapping reifies an annotated annotation assertion with a node
typed `owl:Axiom` (§2.3.1), and the reader reads it so; the reverse mapping of
§3.2.2 would instead take it from a node typed `owl:Annotation`, which the
forward mapping never writes, and such graphs are refused. Reading several
reifications of one main triple, for structurally different axioms with the
same main triple, is not supported, and neither is an annotated annotation
assertion about the ontology IRI, whose triple the header reads as an ontology
annotation. Not proved: that the forward mapping of every ontology is read
back, `owl:imports` closure, that the returned blank nodes are distinct, and RDF
datasets.

`examples/medication-safety-annotated.nt` is the mapping of
`medication-safety.ofn` with its two axiom annotations; the CLI and the
reasoner load it with the same answers as the unannotated graph. Regression
tests read it, a graph with annotations of every kind (nested, on declarations,
on axioms represented by blank nodes, on annotation assertions and on the
header, with reifications before their main triples) with its exact blank-node
order, and refuse reifications without annotations, of missing triples or of
the wrong type.

Looking for reifications costs little: el20000.nt now maps in 0.072 s (0.063 s
after the indexed lookups), and `rowl classify` on it takes 0.40 s with the same
output.

This block adds 24 public theorems and 6 definitions, and removes
`declarations_spec` and `TAnnotation`. Totals are 2644 audited theorems, 1192
definitions, 542 Rust regressions and 2837 ledger obligations.

## M3: reading EL graphs back completely

`map_graph_correct` says that whatever `rdf_mapping::map_graph` reads is right;
the new module `RdfMappingComplete.lean` proves the converse for the EL
fragment. `map_graph_complete`: for every ontology of `ElOntology`, a graph that
lists the triples of the forward mapping of the ontology (`TOntology` of
`RdfMapping.lean`) in its order, as `List.Forall₂ Matches`, with pairwise
distinct blank nodes, is mapped to exactly that ontology, and the returned blank
nodes are exactly those of the forward mapping. `ElOntology` takes ontologies
that are anonymous or named without a version IRI, have no imports or ontology
annotations, and whose axioms are unannotated declarations of any entity and
subclass axioms between `ElClass` expressions: named classes and existential
restrictions of object properties that are `ObjectTyped`, that is declared as
object properties by the axioms and neither declared nor built in as data or
annotation properties. No main triple of an axiom may be about the ontology IRI
(`subjectIri`), because the header reader takes every triple about that IRI with
an annotation property as an ontology annotation. The Rust code is unchanged.

The proof follows the reader. The indexes are complete: `subjects_from_spec`
puts every triple with a blank subject in the bucket of its node, and
`declared_kinds_spec` keeps exactly the declarations of the graph, each in the
bucket of its IRI, so `declared_correct` and `has_kind_correct` decide whether
the graph declares an IRI with a kind, and `object_typed_kind` classifies every
`ObjectTyped` property as an object property. Given all triples about a blank
node at known positions (`Heads`), the lookups find exactly those triples
(`find_hit`, `find_type_hit`). The blank nodes of a construct have all their
unused triples inside its block of the graph (`Owned`, `owned_split`), which
follows from the order and the distinct blank nodes. Each construct is then read
whole and in order, using exactly the positions of its block (`Marked`):
existential restrictions (`existential_complete`), subclass axioms
(`sub_class_complete`), declarations (`read_axiom_declaration`), without
annotations since the graph has no reification (`sources_from_none`,
`annotate_plain`). `axioms_complete` runs the loop of the reader over the blocks
of the axioms, `find_header_at`, `find_header_none` and `header_parts_skip` read
the header, and `all_read_used` checks that nothing is left over.

Not proved: other axioms and class expressions (intersections, inverse
properties and the rest of Table 1), annotations and annotated axioms, version
IRIs, imports and ontology annotations, ontology IRIs punned in subject
position, and graphs in another order; the reader accepts such graphs, as the
regression tests show, but this theorem does not cover them. That the forward
mapping is a function of the ontology up to its blank nodes, and that the
returned blank nodes are distinct, are not proved either.

A regression test builds the forward mapping of an EL ontology with a
restriction on the left of a subclass axiom and nested restrictions, and checks
that it reads back to its axioms in order with its blank nodes in allocation
order. The generated EL benchmark graphs used for the measurements of the last
blocks list their forward mappings in this order.

This block adds 110 public theorems and 5 definitions. Totals are 2754 audited
theorems, 1197 definitions, 543 Rust regressions and 2947 ledger obligations.

## RFC 3986 reference resolution

Turtle resolves relative IRIs against a base, so the kernel now resolves IRI
references by RFC 3986 section 5.2. `references::resolve` splits the reference
and the base into scheme, authority, path, query and fragment by the regular
expression of Appendix B, transforms the reference by the strict algorithm of
section 5.2.2, merging paths as in section 5.2.3 and removing dot segments as in
section 5.2.4, and recomposes the target as in section 5.3. It works on bytes and
looks only at the ASCII delimiters, which is how RFC 3987 section 6.5 resolves
IRIs. `references::is_reference` recognizes RFC 3987 IRI references: plain
relative references by a byte scan, anything else through the validators of
`iri.rs`.

`IriResolution.lean` states the algorithm as functions on words of characters,
written from the RFC: `split`, `transform`, `merge`, `removeDots`, `compose`
and `resolve`, which resolves when the reference or the base has a scheme.
`compose_split` proves that recomposing the Appendix B components gives the
word back. `resolve_opaque` proves that the algorithm commutes with every
spelling that keeps the delimiters `#`, `.`, `/`, `:` and `?` and spells every
other character as a nonempty word without them; UTF-8 is such a spelling
(`utf8_opaque`), so resolving the UTF-8 bytes of IRIs resolves their characters
(`resolve_bytes`, `resolve_scalars`). Against the grammar of `Iri.lean`, whose
language definitions are now public, `iri_parts_iff` and `reference_parts_iff`
characterize IRIs and IRI references by their components, and `split_iri` and
`split_relative` show that the Appendix B split returns exactly those
components. `resolve_iri` proves that resolving an IRI reference against an IRI
gives an IRI whose components are the section 5.2.2 target components whenever
the target has an authority or a path that does not begin with `//`. The
proviso cannot be dropped: `resolve_leaves_iri` shows that the RFC algorithm
resolves `/.//:a` against `a:b` to `a://:a`, which is not an IRI, because
removing the dot segment leaves a path that reads as an authority.

`References.lean` proves the Rust functions against these definitions.
`split_total_correct` proves that `split` returns spans of exactly the Appendix
B components; `remove_dots_total_correct` and `merge_spec` prove the actual
dot-segment removal and merging exact, and `absolute_spec` and `relative_spec`
prove that the two branches of the transformation build exactly the recomposed
target. `resolve_total_correct` proves that on inputs shorter than
`usize::MAX / 8` bytes `resolve` returns exactly `IriResolution.resolve` of
their bytes, and nothing otherwise; the bound leaves room for the output buffer.
`resolve_utf8_iri` composes this with `resolve_iri` for the UTF-8 spellings of
an IRI and an IRI reference. `is_reference_total_correct` proves that
`is_reference` accepts exactly the UTF-8 spellings of RFC 3987 IRI references.
The regression test checks every normal and abnormal example of RFC 3986
section 5.4, the strict reading of `http:g`, the counterexample, absolute
references against a base without a scheme and non-ASCII references.

`remove_dots` dispatches through a classifier whose rungs each have one
condition and ends in one `match`; its extracted body is about 90 kB. Nothing
on the existing reading paths calls the new functions yet, so reading times are
unchanged.

This block adds 80 public theorems and 40 definitions. Totals are 2834 audited
theorems, 1237 definitions, 548 Rust regressions and 3027 ledger obligations.

## RDF 1.1 Turtle reader

`turtle::read` reads a whole RDF 1.1 Turtle document from its UTF-8 bytes into
a raw RDF graph, against a base IRI and a blank-node scope supplied by the
caller; `turtle::read_with_limits` does the same within limits on the bytes of
a term and on the number of triples, and `read` uses `usize::MAX` for both. The
reader covers the grammar of section 6.5: `@prefix` and `@base` and the SPARQL
`PREFIX` and `BASE` in any case, IRIREFs and prefixed names with local escapes,
labelled blank nodes, `[]`, blank node property lists, collections, `a`,
predicate-object and object lists, and every literal: short and long strings
with escapes, language tags, datatypes, integers, decimals, doubles and
booleans. Tokens are the longest matches of the grammar's note, so `true:x` and
`a:b` are prefixed names rather than keywords and a name ends at its last
character that is not a dot. A relative IRI is resolved by RFC 3986 section 5.2
against the base in force (`references::resolve`). Every IRI reference must be
an RFC 3987 IRI reference and every IRI it gives an RFC 3987 IRI; a relative
reference without an absolute base is an error. Language tags must be
well-formed BCP 47 tags. Triples come out in the order of section 7: the triples
inside an object (a blank node property list or a collection) come before the
triple that has the object, and each `rdf:rest` link of a collection before the
triples of the next member. The blank node of a property list that begins at
byte offset `n` has the label `0xFF` followed by the decimal digits of `n`, and
the list node of a collection member at offset `n` the label `0xFE` followed by
them. Document labels are UTF-8 and cannot contain these bytes, and every blank
node has the caller's scope. The reader reuses the N-Triples readers for
characters, white space, comments, escapes, IRIREF and STRING_LITERAL_QUOTE;
`ntriples.rs` only makes nine of its functions visible to the crate.

`TurtleTokens.lean` states the terminals as relations over byte positions,
written from section 6.5 independently of the Rust code: `PrefixColon`
(PNAME_NS), `LocalEnd` (PN_LOCAL with PLX), `Prefixed`, `IriRef`, `IriAt`,
`BlankLabel`, `StringAt` with `SingleBody` and `LongString`, `LanguageAt`,
`LiteralAt` with `DatatypeAt`, `NumberAt`, whose `NumberEnd` gives the end and
datatype of INTEGER, DECIMAL and DOUBLE, `WordObject` for prefixed names and
booleans, and `AtKeyword` and `AnyCase` for the directive keywords. Every token
reader is proved total and exact: a `*_total_correct` theorem states that it
returns exactly what its relation describes or the relation's first error with
its kind and offset, and a `*_accepted` theorem that it reads every token the
relation describes with that value (`iri_ref_total_correct`,
`prefixed_accepted`, `literal_total_correct`, `number_accepted` and so on).

`Turtle.lean` states the productions and their triples as relations:
`NodeAt`, `BracketAt`, `CollectionAt`, `MembersAt`, `ObjectAt`, `ObjectsAt`,
`MoreObjectsAt`, `ListAt` and `MorePredicatesAt` form one mutual family for the
mutually recursive productions; `SubjectAt`, `TriplesAt`, `OpeningAt`,
`PrefixDeclaration`, `BaseDeclaration`, `StatementAt` (with the base and the
prefix declarations in force) and `StatementsAt` follow. `Document bs scope base
termLimit tripleLimit ts` holds when the bytes `bs` are a Turtle document whose
terms fit the term limit and that denotes the triples `ts` in order, at most the
triple limit of them; `DocumentError` gives the first error of any other bytes.
Triples are compared by their terms (`spo`), which determine them
(`spo_injective`). The mutually recursive readers are proved by well-founded
recursion on the remaining bytes and the rank of the production
(`node_total_correct` to `more_predicates_total_correct`, and `node_accepted` to
`more_predicates_accepted`). `read_with_limits_total_correct` proves that
`read_with_limits` returns a graph whose triples are, in order, exactly the ones
the bytes denote, or the first error of the bytes; `read_with_limits_accepted_iff`
proves that it returns a graph exactly when `Document` holds for the graph's
triples. `read_total_correct` and `read_accepted_iff` state the same for `read`.

The relations are written from the Recommendation's grammar and its triple
construction; they are not proved equal to a separate formal reading of the
EBNF. The regression test runs all 313 cases of the W3C RDF 1.1 Turtle suite
(`w3c/rdf-tests` at a pinned commit, file hashes in `turtle-suite.json`,
fetched by `scripts/fetch-turtle-suite.py`), with each document read against
its own URL as the suite's base: positive and negative syntax cases,
negative evaluation cases, and evaluation cases compared with the expected
N-Triples graph up to blank-node isomorphism. All pass. Fourteen further tests
cover the constructs, longest matches, first-error offsets, limits and scopes.
No Turtle document is read into an ontology yet, and Turtle export remains
planned. The 140 Turtle functions extract to 5.5 MB of LLBC; the largest body,
`statement`, has 0.75 MB.

This block adds 303 public theorems and 149 definitions. Totals are 3137
audited theorems, 1386 definitions, 562 Rust regressions and 3330 ledger
obligations.

## Reasoning over Turtle documents

`Reasoner::from_turtle` reads a Turtle document with the verified reader of the
previous section and the OWL ontology its graph encodes with the verified
reverse RDF mapping (`rdf_mapping::map_graph`), exactly as
`Reasoner::from_ntriples` does for N-Triples; a rejected document is
`LoadError::Turtle` with the reader's error. The document gets the scope
`document` and no base of its own, so a relative IRI needs an `@base` or `BASE`
directive before it; `Reasoner::from_turtle_with_base` supplies a base. The
CLI's `check`, `classify` and `instances` commands read `.ttl` files this way,
the C interface has `rowl_reasoner_from_turtle`, and the Python package reads
Turtle with `syntax="turtle"` and `.ttl` files in `Reasoner.from_file`.
`examples/medication-safety.ttl` is the medication-safety example in compact
Turtle, with prefixes, `a`, object and predicate-object lists, blank node
property lists and a collection; like `medication-safety.nt` it leaves out the
two axiom annotations, which the mapping does not read. Rust and Python tests
check that it gives the same classes, individuals, classification and instance
answers as `medication-safety.ofn`, that the reasons for rejected documents are
reported, and that the CLI answers from it and reports the offset of a Turtle
error.

This glue adds no reasoning and no proof; the answers are those of the verified
reader, mapping and queries. Classifying the generated EL ontology with 20 000
classes takes 2.1 s from N-Triples, 3.3 s from the same graph in compact,
subject-grouped Turtle (1.7 MB instead of 7.0 MB) and 14.7 s from Functional
Syntax, with the same answers. Reading takes 0.14 s of the 3.3 s (the N-Triples
reader needs 0.12 s for the N-Triples file, and the Turtle reader 0.20 s for the
same bytes); the rest is mostly the RDF mapping, which takes 1.9 s for the
triples in N-Triples order and 3.8 s in subject-grouped order. Merged with the
hash-indexed RDF mapping, the same classifications take 0.56 s from N-Triples,
0.61 s from compact Turtle and 1.56 s from Functional Syntax on a shared machine,
with identical answers from the two RDF syntaxes.

This block adds 0 public theorems and 0 definitions. Totals are 3137 audited
theorems, 1386 definitions, 566 Rust regressions and 3330 ledger obligations.

## M3: the import catalog from document bytes

The import closure of an ontology (Structural Specification §3.4) needs the
ontology IRI, version IRI and import IRIs of every document it may reach. The
new kernel module `import_catalog` reads them from the bytes of a catalog of
documents that the caller supplies; nothing is fetched. A `Source` is a
document's bytes with its syntax: Functional Syntax, N-Triples, or Turtle with
the base IRI its relative IRIs resolve against. `read_source` reads a document
with its verified reader (`source_reasoning::source_ontology` for Functional
Syntax, `ntriples::read` or `turtle::read` followed by `rdf_mapping::map_graph`
for the RDF syntaxes) into the raw OWL ontology, whose identity and imports are
the document's header. `read_sources` reads every document of a catalog in
order and reports the first one that cannot be read; each document's node IDs
or blank nodes become anonymous individuals of a scope of its own,
`document_scope`, the eight bytes of its position. `names` decides whether an
import IRI is a document's ontology IRI or version IRI, byte for byte (§3.2,
§3.4), `targets` lists the documents an IRI names and `lookup` tells whether it
names none, exactly one or several. `catalog` builds the symbol-indexed catalog
of `imports.rs` from the read ontologies: every document under its position as
its `u32` key, without bytes, with the positions of the documents its import
IRIs name, import by import, so that `imports::resolve` computes the import
closure over it. A catalog with more documents than `u32` keys is refused.

`ImportCatalog.lean` proves these against independent definitions.
`read_source_correct` proves that whatever `read_source` returns is the
reader's result: for Functional Syntax the raw OWL ontology of the bytes
(`SourceReasoning.SourceOntology`), for N-Triples and Turtle the ontology that
the reverse RDF mapping reads from the graph whose triples the bytes denote by
the N-Triples or Turtle grammar (`ReadAs`), or the first error of the reader
(`RejectedAs`). `read_sources_correct` lifts this to a catalog (`AllRead`,
`SourcesCorrect`), and `read_source_functional_total` and
`read_sources_functional_total` prove that Functional Syntax documents are
always read; the reverse RDF mapping has no termination proof, so the RDF
syntaxes are proved correct whenever reading returns. `document_scope_correct`
and `scope_injective` prove that the scopes of different positions differ
(`usize_below` bounds positions). `names_correct` proves `names` exact for
`Names`; `targets_from_correct`, `mem_targets` and `targets_sorted` prove that
`targets` lists exactly the named documents in increasing order, and
`lookup_correct` that `lookup` answers no document, exactly the named one, or
the first two of several (`LookupCorrect`). `catalog_correct` proves that
`catalog` builds a catalog exactly when the documents fit `u32` keys, with
every document under its position and its import targets (`CatalogOf`,
`dependencies_from_correct`). Against §3.4, `DirectlyImports` says that a
document directly imports the documents its import IRIs name and `InClosure`
is its reflexive transitive closure: `catalog_edges` proves that the catalog's
edges are exactly the direct imports, and `catalog_reachable` that its
reachability is exactly the import closure; `catalog_keys_nodup` proves its
keys distinct.

Not done here: resolving and assembling the closure, which the next section
adds, and reading RDF documents with the declarations of the documents they
import (the reverse RDF mapping still needs every entity of a graph declared in
that graph). Six regression tests read a cyclic catalog of Functional Syntax,
N-Triples and Turtle documents, match an import by a version IRI, find missing
and ambiguous imports, read Turtle against its base and report unreadable
documents. Nothing on the existing reading paths calls the module yet. Its 18
functions extract to 0.33 MB of LLBC; the largest, `read_from`, has 46 kB.

This block adds 19 public theorems and 17 definitions. Totals are 3156
audited theorems, 1403 definitions, 572 Rust regressions and 3349 ledger
obligations.

## M3: import closures and their meaning

The axiom closure of an ontology (Structural Specification §3.4) is the union
of the axioms of every ontology in its import closure, with the anonymous
individuals of different ontologies standardized apart (§5.6.2), and the
Direct Semantics interprets that union (§2.4). The new kernel module
`import_closure` assembles it from the catalog of the previous section.
`assemble` takes the ontologies of a catalog, each read in the scope of its
position, and a root position. It builds the catalog, resolves it from the root
with the proved `imports::resolve` and marks the documents it reaches. Every
import IRI of a marked document must name exactly one document; the first that
names none or several, in catalog order, is the error `MissingImport` or
`AmbiguousImport`, with the document and the IRI. Imports of documents outside
the closure do not matter. Every anonymous individual of a marked document must
have the scope of its position, which the new module `anonymous_scopes` checks
over every class expression, axiom, annotation, nested annotation and ontology
annotation (`OutOfScope` otherwise; documents read by `read_sources` never have
one). The closure then has the marked documents in catalog order, the root's
ontology IRI, version IRI and imports, and the ontology annotations and axioms
of the marked documents in that order, every axiom with its document and its
position among that document's axioms (`origins`). The records are moved out of
the read ontologies, not copied. `source_closure` reads a catalog with
`read_sources` and assembles it; nothing is fetched.

`AnonymousScopes.lean` proves the scope checks exact (`scoped_class_correct`,
`scoped_annotation_correct`, `scoped_axiom_correct`,
`scoped_annotated_correct`, `scoped_ontology_correct` against `ScopedClass` to
`ScopedOntology`). Against the Direct Semantics, `class_coincide` and
`axiom_coincide` prove that the extension of a scoped class expression and the
satisfaction of a scoped axiom depend only on what the assignment of anonymous
individuals gives the individuals of the scope, and `models_parts` that for
axiom lists whose anonymous individuals have pairwise distinct scopes, an
interpretation is a model of their concatenation exactly when it is a model of
each list, each with an assignment of its own: they are standardized apart.

`ImportClosure.lean` proves `assemble` total and exact (`assemble_correct`,
`AssembleCorrect`): `NoRoot` exactly for a root outside the catalog,
`TooManyDocuments` exactly beyond `u32` keys, never `Unresolved`, the first
unresolved import of the closure in catalog order (`FirstUnresolved`,
`UnresolvedError`), the first closure document with an anonymous individual
outside its scope, `TooLarge` only when the closure has more axioms or ontology
annotations than a vector holds, and otherwise the closure described above
(`AssembledFrom`), whose documents are exactly the import closure of §3.4
(`ClosureDocuments`, `InClosure`), every import of which names exactly one
document (`ImportsResolved`) and every anonymous individual of which has its
document's scope (`ClosureScoped`). `closure_models` proves that an
interpretation is a model of the assembled axioms exactly when it is a model of
the axioms of every document of the import closure, each document's anonymous
individuals interpreted on their own; `closure_model_iff`,
`closure_consistent_iff`, `closure_entails_iff`, `closure_satisfiable_iff`,
`closure_subsumed_iff` and `closure_instance_iff` restate models, consistency,
entailment, class satisfiability, subsumption and instance checking of the
assembled axioms as those of the import closure (`ImportClosureModel`), so the
reasoner's proved answers on the assembled axioms are answers for the import
closure. `closure_provenance` proves that every axiom of the closure is the
axiom at its recorded origin, in a document of the import closure.
`source_closure_correct` composes the readers and the assembly
(`SourceClosureCorrect`), `source_closure_functional_total` proves that
Functional Syntax catalogs always give a result, and `source_closure_models`
states the meaning of a closure assembled from bytes.

Not done here: reading RDF documents with the declarations of the documents
they import, and checking that the ontology IRIs of the imported documents are
outside the reserved vocabulary; the scopes of documents read by the verified
readers are checked when the closure is assembled rather than proved. Regression
tests assemble a cyclic closure of Functional Syntax and N-Triples documents,
find an import by its version IRI, report missing and ambiguous imports and
foreign scopes, keep colliding node IDs apart, and check the scope traversal on
nested class expressions and annotations. Nothing on the existing reading paths
calls the modules yet; the next section wires them into the reasoner. The 13
functions of `anonymous_scopes` extract to 0.32 MB of LLBC and the 20 of
`import_closure` to 0.95 MB; the largest body, `finish`, has 0.22 MB.

This block adds 23 public theorems and 27 definitions. Totals are 3179 audited
theorems, 1430 definitions, 579 Rust regressions and 3372 ledger obligations.

## Reasoning over import closures

`Reasoner::from_documents` reads the import closure of a root document from a
catalog of documents, each a name for messages, a syntax (Functional Syntax,
N-Triples, or Turtle with a base IRI) and its bytes, with the verified
`import_closure::source_closure` of the previous section, and reasons over the
assembled axiom closure exactly as over a single document. Nothing is fetched.
`LoadError` gains `InDocument` (a document of the catalog the verified reader
rejected, with the reader's error), `MissingImport` and `AmbiguousImport` (the
importing document and the IRI, and for an ambiguous IRI the first two
documents that have it) and `Closure` for the reasons the proofs exclude or
that need more memory than exists. `Reasoner::documents` names the documents of
the closure. `dl_violation` checks the whole axiom closure, so imported
declarations count, and names an offending axiom by its document and its
position there, from the provenance the assembly keeps; of the ontology and
version IRIs only the root's are checked against the reserved vocabulary.

The CLI's `check`, `classify`, `instances` and `validate` commands take
`--imports DIR` (repeatable): the catalog is FILE and every `.ofn`, `.nt` and
`.ttl` file of each DIR, sorted by name, FILE itself left out; the closure's
documents are listed on standard error, and a missing or ambiguous import is an
error naming the document and the IRI. Without `--imports`, a document with
imports is read alone as before, with a note on standard error. The C interface
has `rowl_reasoner_from_documents` with syntax codes, document names, the new
status codes `ROWL_MISSING_IMPORT`, `ROWL_AMBIGUOUS_IMPORT` and `ROWL_CLOSURE`
and the reason in words; the Python package reads closures with
`Reasoner.from_file(path, imports=[...])` (files or directories) and
`Reasoner.from_documents([(name, text, syntax), ...])` and raises
`rowl.ImportUnresolved` for a missing or ambiguous import. Turtle documents of a
catalog are read without a base IRI by the CLI, the C interface and Python.

`examples/imports` splits the medication-safety example into a drug vocabulary
with the alert rule, in Turtle, whose version IRI the prescriptions, in
Functional Syntax, import; `crates/rowl/examples/medication_imports.rs` reads
them. The closure gives the classes, individuals, classification and instance
answers of `medication-safety.ofn`, and is OWL 2 DL, while the prescriptions
read alone use undeclared classes and properties and are not. Regression tests
cover that example, a cyclic closure of Functional Syntax and N-Triples
documents read from two different roots, an import found by its version IRI,
missing, ambiguous and unreadable documents, and colliding blank-node labels in
two documents (Functional Syntax and N-Triples), whose individuals would be in
two disjoint classes were they one: the closure is consistent. The CLI and
Python tests run the same cases through their interfaces.

This glue adds no reasoning and no proof; the answers are those of the verified
readers, assembly and queries. The closure path costs nothing measurable:
classifying the generated EL ontology with 20 000 classes takes 1.15 to 1.29 s
from Functional Syntax and 0.41 to 0.54 s from N-Triples or Turtle on a shared
machine, read alone or as a catalog of one document, with identical output.
`frontend.ImportedDeclarations` stays planned: canonical parsing of an RDF
document needs the declarations of the whole import closure (§3.6 of the
Structural Specification), and the reverse RDF mapping reads each graph with its
own declarations only, so an RDF document of a catalog must declare what it uses.
Documents without an ontology header are not included unless imported or the
root, so `imports.HeaderlessIncludes` stays planned too.

This block adds 0 public theorems and 0 definitions. Totals are 3179 audited
theorems, 1430 definitions, 586 Rust regressions and 3372 ledger obligations.

## M3: Functional Syntax documents lie in their scope

The assembly of an import closure checks that every anonymous individual of a
closure document has the scope of its position, and its meaning rests on that
check. `FunctionalScopes.lean` proves that the check never fails for Functional
Syntax documents. The verified mapping into the raw OWL model turns every node
ID into an anonymous individual of the caller's scope; `class_model_scoped`,
`members_model_scoped` and `rest_model_scoped` prove by mutual induction over
the correspondence relations of `FunctionalModel.lean` that every class
expression it builds is scoped, `annotation_model_scoped` and
`annotations_model_scoped` do the same for annotations with their nested
annotations, `axiom_model_scoped` for every axiom form with its annotations, and
`ontology_model_scoped` for the ontology annotations and axioms of a document.
`source_ontology_scoped` concludes that every ontology read from Functional
Syntax bytes in a scope is scoped by it, and `source_closure_functional_in_scope`
that `source_closure` never reports `OutOfScope` for a catalog of Functional
Syntax documents: for them the standardization apart of the import closure is
proved, not only checked. For N-Triples and Turtle documents the check remains
the guarantee, since the reverse RDF mapping's treatment of blank nodes is only
covered by its soundness theorem against the forward mapping. The Rust code is
unchanged.

This block adds 9 public theorems and 0 definitions. Totals are 3188 audited
theorems, 1430 definitions, 586 Rust regressions and 3381 ledger obligations.

## M3: reading every unannotated readable ontology back

The completeness of the reverse RDF mapping now covers far more than the EL
fragment. Four new modules prove it: `RdfReadIndexes.lean` (the indexes and the
lookups, for triples at arbitrary positions), `RdfReadExpressions.lean` (every
expression reader), `RdfReadAxioms.lean` (every axiom reader) and
`RdfReadOntology.lean` (the header, the axiom loop and the main theorem).
`RdfReadOntology.map_graph_complete`: for every `ReadableOntology`, a graph that
lists the triples of its forward mapping (`TOntology` of `RdfMapping.lean`) in
its order, with blank nodes distinct from each other and from the anonymous
individuals its assertions are about (`FreshSupply`), is mapped to exactly that
ontology, version IRI and imports included, with exactly those blank nodes. The
Rust code is unchanged.

`ReadableOntology` asks for the reserved-vocabulary condition of OWL 2 DL
(`VocabularyOK`) and the typing constraints the reader relies on (`KindTyped`:
every property used is declared or built in as one kind of property only, and no
class is typed as a datatype, so that the reader tells an equivalence of classes
from a datatype definition); no ontology annotations, and no annotation
assertion about the ontology IRI, which the reader takes as an ontology
annotation; and unannotated axioms that are `AxiomReadable`. That covers every
kind of axiom, with class expressions (`ClassReadable`) and data ranges
(`RangeReadable`) of every kind, except three forms that the mapping writes as
triples of other axioms: equivalences of classes or properties and equalities of
individuals of three or more members (written as pairwise triples, read back as
pairwise axioms), inverse-property axioms whose first member is an inverse
(written about a blank node, which the reader takes for an inverse property
expression), and object property assertions on an inverse (written as an
assertion on the property itself). Literals must not be `rdf:PlainLiteral` with
an empty language tag (written as `xsd:string`), cardinalities are at most 10000
(`CARDINALITY_LIMIT`), facets are those of OWL 2 (`owl2Facets`), and the datatype
of a datatype definition is declared or built in.

The proof works with blocks of triples at arbitrary positions rather than
consecutive ones (`Ready`, `At`): the subject index is complete, the positions of
a block are unused and hold its patterns, and every unused triple about one of
its blank nodes is at one of its positions. On that footing every expression
reader is complete (`class_reads` and `range_reads`, mutually recursive over all
class expressions and data ranges, the list readers `cells_complete`,
`class_list2_complete`, `property_list2_complete`, `data_list2_complete`,
`key_members_complete` and the rest), and so is every axiom reader, from its main
triple, through the dispatch on predicate and type (`read_axiom_*`, `typing_*`),
using exactly the positions of its block and recording exactly its blank nodes,
without annotations (`annotate_plain`, and `annotate_blank` for the axioms that a
blank node represents): `axiom_reads`. `block_shape` describes the triples of
each block, `graph_kinds` shows that the declarations of the graph type every IRI
as the ontology does, `header_parts_imports` reads the imports, and
`axioms_loop` runs the reader's loop over blocks in the order of their main
triples, passing over used triples and over triples of later blocks.

Not proved: annotated axioms and ontology annotations, graphs in another order
(`axioms_loop` already allows triples of a block before its main triple, provided
the reader passes over them, which is not yet shown), several reifications of one
main triple, imports closure, and RDF datasets. The EL theorem of
`RdfMappingComplete.lean` stays for EL ontologies that do not satisfy the
vocabulary conditions.

The regression test `readable_graphs_in_forward_order_read_back_exactly` reads
`crates/rowl-kernel/tests/data/dosing.nt`, the forward mapping of
`crates/rowl-kernel/tests/data/dosing.ofn` with every kind of axiom, class
expression and data range, and checks that it reads back to the ontology the
Functional Syntax reader reads from `dosing.ofn`, axiom by axiom, with the 71
blank nodes in allocation order. The dosing fixtures combine constructs that
OWL 2 DL forbids together (a self restriction and a disjointness axiom on
non-simple properties), so they live with the kernel tests rather than among
the examples, which are all OWL 2 DL.

This block adds 479 public theorems and 15 definitions. Totals are 3667 audited
theorems, 1445 definitions, 587 Rust regressions and 3860 ledger obligations.

## M3: reading graphs in any order

Real graphs list their triples in any order, while the completeness theorem of
the last block asked for the order of the forward mapping. The new module
`RdfReadPermuted.lean` proves `RdfReadPermuted.map_graph_complete_perm`: for
every `ReadableOntology`, a graph whose triples are a permutation of triples
that instantiate the forward mapping (`TOntology`) in order, with blank nodes
as in `FreshSupply`, is mapped to that ontology, with the same identity, version
IRI and (empty) annotations, the same imports and axioms up to their order, and
the blank nodes of the forward mapping up to their order. The axioms come out in
the order of their main triples and the imports in the order of their triples.
The Rust code is unchanged: nothing in the reader depended on the order.

The proof follows the reader. `perm_positions` turns the permutation into
positions of the forward patterns in the graph, and `position_blocks` cuts the
positions of the axioms into blocks, which `sortBlocks` orders by their main
positions for `axioms_loop` of the last block. That loop needs the reader to
pass over a triple of a block met before its main triple: such a triple belongs
to an expression or a list, about one of the block's blank nodes, and
`side_skip` shows that `read_axiom` returns `Skip` for it, through the
reserved, non-dispatched predicates of expressions and lists
(`side_predicates_structural`, `read_axiom_structural`), the typing of a
restriction, class or datatype node (`typing_blank`) and inverse property
expressions; `block_rest_skip` applies this to every block. For the header,
`find_header_first` finds the one triple typing an IRI `owl:Ontology` wherever
it is (the triples of axioms never type an IRI so, `block_not_ontology`), and
`header_parts_rest` shows that `header_parts` takes the version IRI and the
imports wherever they are and passes over every other triple
(`header_parts_passed`, `header_parts_elsewhere`, `header_parts_other`,
`header_parts_import`), using exactly their triples, with the imports up to
order.

Not proved: annotated axioms and ontology annotations (as before), graphs that
repeat a triple, several reifications of one main triple, imports closure and
RDF datasets.

The regression test `readable_graphs_in_any_order_read_back_up_to_order` reads
`crates/rowl-kernel/tests/data/dosing.nt` in reverse order and in twelve
shuffled orders and checks that each reads back to the ontology of
`crates/rowl-kernel/tests/data/dosing.ofn`: the same identity
and version IRI, the import, the 80 axioms up to order (compared with
`same_axiom`) and the 71 blank nodes up to order. Mapping the generated
20 000-class graph `el20000.nt` (64 081 triples) takes about 0.09 s in its own
order and in a shuffled one alike (median of five runs each, 87 ms and 86 ms).

This block adds 26 public theorems and no definitions. Totals are 3693 audited
theorems, 1445 definitions, 588 Rust regressions and 3886 ledger obligations.

## M3: reading annotated ontologies back

The completeness of the reverse RDF mapping now covers ontology annotations and
annotated axioms. `RdfReadAnnotated.map_graph_complete_annotated`: for every
`ReadableAnnotated` ontology, a graph that lists the triples of its forward
mapping (`TOntology`) in order, with blank nodes as in `FreshSupply`, is mapped to
exactly that ontology, its annotations and the annotations of its axioms in
order included, with exactly those blank nodes. The Rust code is unchanged.

`ReadableAnnotated` keeps the conditions of `ReadableOntology` for the axioms and
allows annotations without annotations of their own (`PlainAnnotations`, with
literal values the reader reads back) on the ontology and on axioms with one
main triple (§2.3.1). Such an axiom is written as its triples followed by the
`owl:Axiom` reification of its main triple and the annotation triples of the
reifying node. An annotated axiom must occur in the ontology only once: the
reader takes the first reification of a main triple it finds, so two copies of
an axiom, one annotated, would exchange their annotations.

Two new modules prove it. `RdfReadAnnotations.lean` proves the readers of
annotations complete: the source index lists every `owl:annotatedSource` triple
(`sources_from_spec`) and the subject index lists the positions of each blank
node in increasing order (`subjects_from_sorted`); `reifier` finds the
reification of a triple when no other blank node reifies the same triple
(`reifier_found`) and nothing when none does (`reifier_absent`); and
`node_annotations` reads the annotations of a blank node in the order of their
triples (`node_annotations_plain`). `RdfReadAnnotated.lean` reads the axioms of
the ontology without annotations (`strip`, `readable_strip`) with the reader of
the last blocks, made independent of the source index (`axiom_reads_core` in
`RdfReadAxioms.lean`, from which `axiom_reads` now follows). The key step is
`agraph_exclusive`: a blank node that reifies the main triple of an axiom is
the reifying node of that axiom, because two blocks with the same main triple
read as the same axiom (the reader is a function, and the main triple of the
one block can stand in for that of the other) and an annotated axiom occurs
once. With it, `agraph_step` reads each block with its annotations,
`annotated_loop` runs the axiom loop over the blocks, and
`header_parts_annotations` reads the ontology annotations in the header.

Not proved: annotations of annotations (`owl:Annotation` reifications),
annotated axioms that a blank node represents (disjointness and difference of
three or more, negative assertions; the reader reads their annotations from that
node, but the proof of the axiom readers asks that no other triple be about it)
and annotated equivalences of three or more members, annotated graphs in another
order, several reifications of one main triple, imports closure and RDF
datasets. The ledger entries `frontend.RDFStructuralMapping` and
`frontend.AnnotationReification` stay implemented: the reader still refuses
several reifications of one main triple and cardinalities above 10000, so no
theorem covers those requirements in full.

The regression test `annotated_graphs_in_forward_order_read_back_exactly` reads
`crates/rowl-kernel/tests/data/dosing-annotated.nt`, the forward mapping of
`crates/rowl-kernel/tests/data/dosing-annotated.ofn` (the dosing example with two
ontology annotations and annotations on 18 axioms, among them an IRI, an anonymous
individual and an `xsd:string` literal as values), and checks that it reads back
to the ontology of the Functional Syntax reader, annotations in order, with the
83 blank nodes in allocation order; twelve of the annotated axioms have one main
triple, and the six that a blank node represents, outside the theorem, are read
as well. Shuffled in five orders, the graph reads back to the same axioms up to
order, which no theorem covers yet.

This block adds 94 public theorems (three of them in `RdfReadAxioms.lean`) and 4
definitions. Totals are 3787 audited theorems, 1449 definitions, 589 Rust
regressions and 3980 ledger obligations.

## M3: reading annotated graphs in any order

The completeness of the reverse RDF mapping for annotated ontologies now holds
for graphs in any order. `RdfReadAnnotatedPermuted.map_graph_complete_annotated_perm`:
for every `ReadableAnnotated` ontology, a graph whose triples are a permutation
of the triples of its forward mapping (`TOntology`), with blank nodes as in
`FreshSupply`, is mapped to that ontology: the same identity and version IRI,
the same imports, ontology annotations and axioms up to their order, each axiom
with its annotations up to their order, and the blank nodes of the forward
mapping up to their order. The Rust code is unchanged.

In another order the axiom loop can meet the reification of an annotated axiom
and the annotation triples of its reifying node before the main triple.
`agraph_skip` shows that `read_axiom` passes over all of them: the triple typing
the reifying node `owl:Axiom` is no typing the reader takes for an axiom
(`typing_reifier_blank`), the triples with the predicates `owl:annotatedSource`,
`owl:annotatedProperty` and `owl:annotatedTarget` are structural
(`read_axiom_reification_skip`), and an annotation triple of a blank node typed
`owl:Axiom` is left to the axiom that the node annotates (`read_axiom_head_skip`,
which finds the typing triple through the subject index, `reifier_subject_true`).
At the main triple, `annotate` reads the annotations of the reifying node
wherever their triples are, in the order of their positions
(`node_annotations_any` in `RdfReadAnnotations.lean`), a permutation of the
annotations of the axiom; `annotated_loop_perm` runs the loop over the blocks
sorted by their main positions (`sort_ablocks_sorted`). In the header,
`header_parts_rest_a` takes the version, the imports and the ontology
annotations wherever they are.

For this, the facts about the blocks of the graph (`AGraph`) and the reading of
a block (`agraph_step`) in `RdfReadAnnotated.lean` now hold for blocks at any
positions of the graph: `agraph_step` returns the annotations of a block up to
their order, and in their order when the annotation triples of the block come
in order (`ABlock.Ordered`), which `map_graph_complete_annotated` uses; its
statement is unchanged.

Not proved: annotations of annotations, annotated axioms that a blank node
represents and annotated equivalences of three or more members, several
reifications of one main triple, repeated triples, imports closure and RDF
datasets. The ledger entries `frontend.RDFStructuralMapping` and
`frontend.AnnotationReification` stay implemented, for the reasons of the
previous section.

The regression test `annotated_graphs_in_any_order_read_back_up_to_order` reads
the triples of `crates/rowl-kernel/tests/data/dosing-annotated.nt` in reverse
order, where every reification and annotation triple comes before the axiom it annotates, and in
twelve shuffled orders, and checks the identity and version IRI, the imports,
the ontology annotations up to order, the axioms up to order with their
annotations up to order, and the 83 blank nodes up to order. The five shuffled
orders that `annotated_graphs_in_forward_order_read_back_exactly` checked move
to this test. The new module checks in about 10 s with a peak under 3 GiB.

This block adds 27 public theorems (two of them in `RdfReadAnnotations.lean` and
one in `RdfReadAnnotated.lean`) and no definitions. Totals are 3814 audited
theorems, 1449 definitions, 590 Rust regressions and 4007 ledger obligations.

## M3: N-Triples and Turtle writers, proved by round trips

`rdf_write.rs` replaces the experimental N-Triples writer with one writer for
N-Triples and a canonical subset of Turtle: `ntriples::write` and
`turtle::write` call `rdf_write::write_graph`, which first looks for a term the
syntax cannot carry and then writes within the output-byte budget. Each triple
is the line `subject predicate object .`; an IRI is an IRIREF that holds raw the
characters an IRIREF may hold and writes the others as UCHARs `\U` with eight
uppercase hexadecimal digits; a string writes `"`, `\`, line feed and carriage
return as ECHARs and every other character raw; every literal carries its
datatype or its language tag; a blank node of the scope `s` and the label `l` is
`_:b`, the two lowercase hexadecimal digits of each byte of `s`, `_` and those of
`l`. N-Triples cannot carry an IRI that is not an absolute RFC 3987 IRI, a
lexical form that is not UTF-8, the datatype rdf:langString, or a tag that is
not a well-formed BCP 47 tag of LANGTAG's form; the Turtle writer also rejects,
with the new `WriteError::IriChangedByResolution`, an IRI that RFC 3986 section
5.2 resolution changes, since Turtle resolves every IRIREF and the subset uses
no prefixed names. Every line is also a Turtle statement, so the Turtle writer
writes the same bytes for the graphs it accepts.

`RdfWrite.lean` writes the text (`LinesText`, `TripleText`, `IriText`,
`StringText`, `BlankText`, `WrittenLabel`) and the faults (`IriFault`,
`LiteralFault`, `TripleFault`, `GraphFault`) as Lean functions of the graph,
independently of the writer, and proves every writer function against them:
`write_graph_total_correct`, `ntriples_write_total_correct` and
`turtle_write_total_correct` state that the writers always return, with exactly
`LinesText` of the triples when no term is at fault and the text fits the
budget, the first fault in triple order otherwise, and `ResourceLimit` when the
text is longer than the budget.

`RdfWriteRead.lean` composes them with the verified readers.
`ntriples_write_read`: the bytes `ntriples::write` returns are read by
`ntriples::read`, in any blank node scope, as the graph's triples in order, each
blank node becoming the blank node of the reader's scope labelled
`WrittenLabel` of its scope and label (`renameTerm`). `turtle_write_read` proves
the same through `turtle::read` against every base IRI shorter than
`usize::MAX / 8` bytes (`resolves_any_base`: an IRI that resolution leaves
against the empty base has a scheme and resolves to itself against every base).
`written_label_injective` makes the renaming one to one, so the graph read back
is the written graph up to a blank node bijection. The proofs derive the reader
relations of `NTriples`, `TurtleTokens` and `Turtle` for the written bytes
position by position: UCHAR digits (`hex_read`), IRIREF and string bodies
(`iri_body_read`, `string_body_read`), labels (`blank_token_read`,
`turtle_blank_read`), tags (`tag_token_read`, `turtle_tag_read`), literals,
lines and documents (`lines_read`, `turtle_lines_read`). The N-Triples writer's
faults are exact: `document_writable` proves that every N-Triples document,
under any limits, denotes triples without faults (`xsd_string_absolute` shows
that the datatype of simple literals is an absolute IRI), and
`ntriples_write_error_exact` concludes that when the writer reports a fault, no
graph that `ntriples::read` returns agrees with the graph up to blank nodes. The
Turtle writer's `IriChangedByResolution` is a limit of its subset, not of Turtle,
which can carry some such IRIs through prefixed names; the other Turtle faults
are N-Triples faults, but no theorem yet states that no Turtle document carries
them. Graph export is now verified for both syntaxes (`format.NTriplesExport`,
`format.TurtleExport`); `format.RepresentabilityErrors` concerns RDF/XML and
JSON-LD and stays planned.

Seven regressions in `crates/rowl-kernel/tests/writers.rs` read written graphs
back through both readers, check every fault kind, the first fault before an
exhausted budget, dot segments kept in N-Triples and rejected in Turtle, and
budgets of exactly the written length. All 68 W3C N-Triples cases still pass,
every positive case written by the new writer and read back to an isomorphic
graph (`rowl-frontend`'s suite test with the fetched corpus).

This block adds 223 public theorems and 45 definitions. Totals are 4037 audited
theorems, 1494 definitions, 597 Rust regressions and 4230 ledger obligations.

## M3: XML documents for RDF/XML

`xml.rs` reads the UTF-8 bytes of an XML document into the element tree that
RDF/XML reads (RDF 1.1 XML Syntax §6). `XmlGrammar.lean` states, independently
of the reader and over words of code points, the productions of XML 1.0 (Fifth
Edition) that the supported documents use and the constraints of Namespaces in
XML 1.0 (Third Edition). Every production is a relation between a word and what
it yields: the element tree, whose elements have their prefix, namespace name
and local name, their attributes in document order with normalized values, their
own namespace declarations and their children, where each maximal run of
characters is one text node and comments and processing instructions give
nothing; and the cost of the entity expansions, one plus the length of the
replacement text for each. `Decoded` reads bytes as strict UTF-8 whose
characters are all `Char`s, drops a leading byte order mark (§4.3.3) and
normalizes line ends (§2.11). `Document` is production [1]: a prolog, one
element under the well-formedness constraints Element Type Match, Unique Att
Spec, No < in Attribute Values, Legal Character, Entity Declared, Parsed Entity
and No Recursion, and Misc. `Read bytes budget root` says that the decoded
characters derive a document with root `root` whose expansions cost at most
`budget`.

The supported documents are the well-formed ones whose encoding declaration,
when present, names UTF-8, whose internal subset holds only entity declarations,
comments, processing instructions and white space, and whose entity references
name declared internal entities or predefined ones. An external identifier of
the document type declaration is not read. Declarations of the five predefined
names never change them. Attribute values are normalized as for CDATA
attributes, character references and entity replacement texts included
(§3.3.3). Element and attribute names are QNames resolved under every namespace
constraint: Reserved Prefixes and Namespace Names, Prefix Declared, No Prefix
Undeclaring and Attributes Unique. Element type, attribute-list and notation
declarations, parameter-entity references, other encodings and references to
external, unparsed or undeclared entities are declined with typed errors; an
attribute-list declaration would change the infoset through defaults and
normalization.

`Xml.lean` proves `read_correct`: when the byte length plus the budget fits in
`usize`, `xml::read` returns the tree `root` exactly when `Read bytes budget
root` holds, and returns an error exactly when no tree is read. `read_unique`
follows: a document has at most one tree. `read_total` proves that `read`
always returns. On the characters, `document_sound` and `document_complete`
relate `xml::document` to `Document`; `decode_spec` proves that `decode`
returns exactly the decoded characters, which are unique (`textFrom_unique`),
and `byte_offset_total` that mapping an error position back to a byte offset
never fails. Error kinds and offsets are reported but not specified by the
theorems.

Each function has a soundness theorem, proved by well-founded recursion on the
remaining characters, saying that it returns, and that a successful result
comes with a derivation of the word it consumed; and a completeness theorem,
proved by induction on derivations, saying that it returns the derived value
when the characters that follow the word cannot extend it. Elements, content
and markup are mutually recursive in the grammar; their completeness proofs are
mutual structural recursions over the derivations. The entity stack makes
references to an entity inside its own expansion an error, which is the No
Recursion constraint, and the budget bounds the expansions, so the
billion-laughs document of the tests stops with a resource error.

This block adds 502 public theorems and 84 definitions. Totals are 4539 audited
theorems, 1578 definitions, 601 Rust regressions and 4732 ledger obligations.

## M3: RDF/XML graphs

`rdfxml.rs` reads the element tree of `xml::read` into a raw RDF graph, following
RDF 1.1 XML Syntax (W3C Recommendation, 25 February 2014). `RdfXmlGrammar.lean`
states sections 5 to 7 as relations over element trees, written independently
of the reader. An element becomes an element event whose URI is its namespace
name followed by its local name (§6.1.2). The attributes with reserved XML names
are dropped, the names ID, about, resource, parseType and type without namespace
are read in the RDF namespace, other names without namespace are errors, and the
remaining attributes keep their namespace name and local name (§6.1.4); no
namespace name may extend the RDF namespace name, and no two attribute events of
an element may have the same URI. An
element's `xml:base` is resolved against the base IRI of its parent by RFC 3986
section 5.2 (`IriResolution.resolve`), starting from the caller's base IRI, and
`xml:lang` sets the language of the element and its descendants.

The productions of section 7 relate an element, read in a context and from a
state, to the triples it adds, in an order fixed by the relations, and to the
state after them: the number of generated blank nodes and the `rdf:ID` values
with their base IRIs, each of which must be new (constraint-id, §5.4). Node
elements take their subject from `rdf:ID`, `rdf:nodeID`, `rdf:about` or a
generated blank node, add an `rdf:type` triple unless they are
`rdf:Description`, and one triple per property attribute. Property elements are
resource, literal, `parseType="Resource"`, `parseType="Collection"` and empty
ones; `rdf:li` numbers them per node, and `rdf:ID` on a property element
reifies its statement (§7.3). Generated blank nodes are labelled with the byte
0xFF followed by the decimal digits of a counter, which no UTF-8 `rdf:nodeID`
label contains, and every blank node is in the caller's scope, as for N-Triples.
An empty property element with `rdf:datatype` has the empty literal of that
datatype (the RDF 1.1 erratum "Allow datatyped empty literals"). The datatype
IRI is the value of `rdf:datatype` as written (§7.2.16) and must be an IRI other
than `rdf:langString`. `rdf:parseType="Literal"` and the other values read as
Literal have no relation: the XML literal needs XML canonicalization, which is
not specified, and the reader declines them with `UnsupportedParseType`.
`Graph` says that a tree derives the triples `ts` within a limit on the bytes of
each term and a limit on the triples, generated blank nodes and `rdf:ID` values.

`RdfXml.lean` proves `graph_correct`: when the term limit is positive and below
`usize::MAX / 8`, `rdfxml::graph` returns exactly the triples, in order, that
the grammar derives for the tree, and an error exactly when it derives none, so
the grammar determines the triples (`graph_unique`). `read_correct` composes
this with `Xml.read_correct`: when the byte length plus the expansion budget
also fits in `usize`, `rdfxml::read_with_limits` returns a graph exactly when
`XmlGrammar.Read` reads a tree from the bytes and the tree has a graph, with its
triples; an XML error exactly when no tree is read; and an RDF/XML error
otherwise. `read_total` proves that it always returns. Error kinds are reported
but not specified by the theorems.

Node elements, property element lists, property elements, the bodies of the
productions and collections are mutually recursive in the grammar and in the
reader. Their correctness is one mutual recursion over the element tree, well
founded on the size of the element, the place of the function in the calls and
the remaining children. Each function has one theorem in both directions: a
result comes with a derivation, and a derivation within the limits gives that
result. The functions they call are proved first, by recursion on positions
(`RdfXmlTerms`, `RdfXmlEvents`, `RdfXmlProps`). The regressions run the examples
of section 2 of the Recommendation, the productions and documents without a
graph. A run of the W3C RDF 1.1 XML Syntax test suite outside the repository,
comparing graphs up to blank node renaming, passed 123 of the 126 evaluation
cases, the three others being the cases with `rdf:parseType="Literal"`, and
rejected all 40 negative cases; no runner for it is committed yet.

Not done yet: `Reasoner::from_rdfxml`, the command line choosing the reader by
extension (`.owl`, `.rdf`) or content, the C interface, the Python package and
import catalogs with RDF/XML documents, a regression that reads an OWL example
in RDF/XML against the same ontology in N-Triples, a committed W3C suite runner,
and a measurement of reading speed; `rdfxml::read` with default limits is not
written either, so callers pass `Limits` to `read_with_limits`.

This block adds 334 public theorems and 66 definitions. Totals are 4873 audited
theorems, 1644 definitions, 605 Rust regressions and 5066 ledger obligations.

## M5: Keys with object properties in the ontology queries

The ontology queries now answer for closures with keys whose properties are
object properties. A key `HasKey(CE (P1 … Pm) ())` says that two named instances
of `CE` that share a named `Pi`-value for every `i` are equal (Direct
Semantics §2.3.5). `data_ontology::prepare` hands a closure with a key to the
new `key_ontology::prepare`, which encodes the keys into SROIQ axioms next to
the data encoding of the other axioms, so the completion forest decides them;
closures without keys take the same path as before.

The encoding asserts a fresh class `N` (the name `[0, K]`) at every named
individual of the closure, those of the keys' class expressions included, with
`N` kept apart from the data nodes, and asks every key of the elements of `N`
only. A key with one property `P`, in a closure without transitive properties
and property chains (so that `P` is simple), becomes
`N ⊑ ≤1 P⁻.(CE' ⊓ N)` for the encoding `CE'` of its class expression: a named
value has at most one named instance of `CE` as its `P`-predecessor
(`countedAxiom`). Every other key gets a role `mark` whose self loops mark the
elements of `N` (`N ⊑ ∃mark.Self`), for each property the chain
`Pi ∘ mark ∘ Pi⁻ ⊑ share(Pi)` (two elements that share a named `Pi`-value), and
at every named individual `x` the assertion
`x : ∀share(P1).(¬N ⊔ ¬CE' ⊔ {x} ⊔ ∀share(P2)⁻.¬{x} ⊔ … ⊔ ∀share(Pm)⁻.¬{x} ⊔ ∀share(P1)⁻.(¬{x} ⊔ ¬CE'))`.
Its last disjunct says, at an element that shares a value with `x`, that `x`
is not in `CE`, so the forest splits on `CE` at `x` only where some element
shares a value with `x`. The form `x : ¬CE' ⊔ ∀share(P1).(…)` with the split at
every named individual took 214 s on 51 patients with a two-property key and a
contradicting inequality (debug build); this form takes 1.1 s.

`IsInterpretation` only requires the individuals of the vocabulary to be
named, and keys apply only to named individuals, so the answers are the Direct
Semantics answers for every vocabulary that names the closure's individuals:
`NamesKeyed V items` asks that every named individual of a closure with keys,
its keys' class expressions included, be an individual of `V`, and asks
nothing of a closure without keys, so the query theorems keep their strength
there.

`KeyEncoding.lean` specifies the actual kernel functions and what their axioms
say: `counted_holds`, `chain_holds` and `shared_holds` give the meaning of the
three axiom forms, `key_axioms_spec` and `keys_from_spec` prove `KeysMeans`
(in an interpretation that satisfies the key axioms with the closure's named
individuals in `N` and marked, every key holds for those individuals; and the
axioms hold in every interpretation in which `mark` and `share` have their
intended structure and the key holds for the elements of `N`),
`encode_meaning` describes the whole encoding and `closure_nodes` proves that
the kernel collects exactly the individuals the closure names.
`KeyModels.lean` builds the models: `keyed_encoded_model` turns a model of the
encoding into an OWL model of the closure whose named elements are exactly the
closure's named individuals (`keyedSound`, the data encoding's interpretation
with the other named individuals placed at the first of them), and
`keyed_lifted_model` lifts an OWL model for a vocabulary that names the
closure's individuals to a model of the encoding (`liftedN`: `N` the named
elements, `mark` their self loops and those of the data values, `share(P)` the
pairs that share such an element along `P`); in both, every question whose
individuals the closure names holds exactly where its encoding does.
`DataOntology.lean` proves the dispatch (`key_prepare_correct`,
`prepare_in_correct`) and states `consistent_correct`,
`class_satisfiable_correct`, `subsumed_correct`, `instance_of_correct` and
their prepared forms with the `NamesKeyed` hypothesis; an instance question
about a closure with keys must name an individual the closure names
(`named_known_spec`), else it gets no answer. `Classification.classify_correct`
and the source queries of `SourceReasoning.lean` carry the hypothesis along.

The kernel module is `crates/rowl-kernel/src/key_ontology.rs`;
`data_ontology.rs` gets the `Prepared::Keyed` variant, the dispatch, the keyed
arms of the prepared queries and `named_known`, and makes a few helpers
`pub(crate)`. Twelve regression tests (`crates/rowl-kernel/tests/key_ontology.rs`)
cover two patients with the same named insurance id, who become equal and
share their classes, and are different without the key; an asserted
`DifferentIndividuals`, which makes the closure inconsistent; keys that apply
only to instances of the key class and never to anonymous individuals or
through unnamed values (an anonymous value, and a value that only an
existential restriction provides); a key that resolves a disjunction; keys with
several properties, which need every value shared; keys on inverse and
transitive properties; nominals in key classes; prepared queries; and the keys
that get no answer.

Not done: keys with a data property, a key with no property or the universal
role, and instance questions about individuals the closure does not name get
no answer. Data-property keys need, in the model made from a model of the
encoding, values of the named elements that differ unless their data nodes are
the same literal node (the data encoding's values are chosen per element and
may coincide across elements); with the five datatypes every boolean data node
is one of the two truth literal nodes already. The ledger entries
`calculus.KeysNamedSubjects` and `calculus.KeysNamedObjectValues` stay planned,
like the other calculus entries, until full OWL 2 DL is covered.

Before this block a closure with a key got no answer. With it, `rowl check`
(release build, shared machine) on generated closures of `n` patients with
named insurance ids, one more patient sharing the first one's values, and an
inequality between the two that makes the closure inconsistent takes, for
`HasKey(:Patient (:hasInsuranceId) ())` (the counted form), 0.47 s for
`n = 100`, 19.6 s for `n = 400` (22.4 s without the inequality) and 320 s for
`n = 1000`; for `HasKey(:Patient (:hasInsuranceId :hasBirthDate) ())` (the
shared form) 0.45 s for `n = 50`, 1.6 s for `n = 100` and 13.0 s for `n = 200`
(11.6 s without the inequality). The cost grows with the number of named
individuals, each of which is a node of the completion forest; closures
without keys are unaffected.

This block adds 128 public theorems and 36 definitions. Totals are 5001
audited theorems, 1680 definitions, 617 Rust regressions and 5194 ledger
obligations.

## M5: numeric datatypes and range facets on single values

`Rowl.DatatypeMap.Normative` now also specifies the other OWL 2 numeric
datatypes, from the OWL 2 Structural Specification §4.1 and XML Schema 1.1
Part 2: `owl:real`, `owl:rational` and the twelve subtypes of `xsd:integer`
(`xsd:nonNegativeInteger`, `xsd:nonPositiveInteger`, `xsd:positiveInteger`,
`xsd:negativeInteger`, `xsd:long`, `xsd:int`, `xsd:short`, `xsd:byte`,
`xsd:unsignedLong`, `xsd:unsignedInt`, `xsd:unsignedShort` and
`xsd:unsignedByte`), and the range facets `xsd:minInclusive`,
`xsd:maxInclusive`, `xsd:minExclusive` and `xsd:maxExclusive`. Numbers can now
denote reals: a normative map has an injective embedding `real` of the reals,
apart from strings, tagged strings and truth values, whose restriction to the
rationals is the existing number embedding (`real_number`). `owl:real` has the
reals as its value space and no lexical forms; `owl:rational` has the
rationals, written `numerator/denominator` with an integer numeral and a
positive digit string (RationalForm); each subtype has the integers within its
XML Schema bounds (Bounded, integerSubtypes) and their integer numerals. The
facet space of `owl:real` and `owl:rational` pairs the four facets with every
real, that of the XML Schema numeric datatypes with the values of the datatype
(xsdNumericTypes, rangeFacets), and the facet values are the same for every
datatype: the reals at least, at most, above or below the bound. A model map
over the reals satisfies the extended specification (modelMap,
modelNormative), so it is not contradictory.

The Direct Semantics specification (`OwlSemantics.lean`) changes in one point.
Its `DatatypeMap` asked, after §2.1, that a facet value lie in the value space
of every datatype whose facet space has the pair (`facetInSpace`). Read
literally that is contradictory for numbers: the pair of `xsd:minInclusive` and
0 is in the facet spaces of both `owl:real` and `owl:rational`, so its facet
value would contain no irrational number, while `owl:real[>= 0]` must contain
every nonnegative real. Table 4 intersects a datatype restriction with the
datatype's value space anyway, so with facet values shared by all datatypes a
restriction denotes exactly the facet values of §4.1. The field is removed. No
theorem used it as a hypothesis, so every theorem about all datatype maps now
covers more maps. The theorems stated under `Normative` keep their statements;
`Normative` now also fixes the new datatypes and facets, as every OWL 2
datatype map does.

The kernel computes with numbers exactly. `numbers` works on natural numbers
written as ASCII decimal digit strings, most significant digit first, and
`Rowl.Numbers` proves every operation correct on their values (digitsValue):
canonical forms without leading zeros (canonical_spec), comparison
(compare_naturals_spec), addition and subtraction digit by digit, schoolbook
multiplication, division with remainder by at most nine subtractions per
digit, Euclid's greatest common divisor and multiplication by powers of ten
(add_naturals_spec, subtract_naturals_spec, multiply_naturals_spec,
divide_naturals_spec, gcd_naturals_spec, times_power_spec, ten_power_spec), for
inputs whose lengths stay within a `usize` limit.

`datatypes::literal_value` reads literals of nineteen datatypes (kind_of_correct;
the kinds are tested one by one, kind_from_correct). The subtypes take integer
numerals within their bounds (bounded_value_correct, lower_bound_correct,
upper_bound_correct). An `owl:rational` literal is reduced to lowest terms
with the greatest common divisor; it becomes a decimal number when its
denominator then divides a power of ten, so `"1/4"^^owl:rational` and
`"0.25"^^xsd:decimal` are one value, and otherwise a new kernel value
`Fraction` of its sign, numerator and denominator (rational_value_correct,
CanonicalFraction). Values stay canonical, so equal values are equal kernel
values (value_injective), and membership of a value in each of the nineteen
value spaces is exact (in_kind_correct, normative_in_kind). `compare_values`
orders two numbers by their signs and then their magnitudes: two decimals digit
by digit, otherwise by cross-multiplying numerators and denominators
(compare_numbers_spec, compare_values_correct). `facet_holds` evaluates a range
facet with a numeric bound on a number (facet_holds_correct), which under every
normative map is membership in the facet value (normative_facet), and
`facet_applies` decides whether a facet with a bound is in the facet space of a
datatype (facet_applies_correct). The regressions compare the digit-string
arithmetic with `u128` arithmetic on sampled operands and check the new
literals, bounds, orders and facets (`tests/numbers.rs`, `tests/datatypes.rs`).

Statements that changed: kind_value_correct and literal_value_correct allow no
answer for an `owl:rational` lexical form of `usize::MAX / 16` bytes or more,
where the kernel gives up before forming products; in_kind_correct assumes a
canonical value, since a subtype's bounds are checked by comparison, and so do
DataStructure's kind_member_spec and value_axioms_spec for the literal values
of the context, which `Good` contexts have; DataSound's region lemmas
(number_kind, text_kind, tagged_kind, region_space) are stated for the five
datatypes the encoding uses (Classic).

The ontology queries take literals of all nineteen datatypes as values: a data
property assertion with `"300"^^xsd:short` or `"1/3"^^owl:rational` is
answered, under every datatype map that is the OWL 2 map on these datatypes.
Data ranges naming the fourteen new datatypes, and datatype restrictions, still
get no answer, and the umbrella ledger entries of these datatypes and facets
stay planned; encoding them is the next stage. Reasoning is otherwise
unchanged, so there is nothing new to measure.

This block adds 156 public theorems and 55 definitions. Totals are 5157
audited theorems, 1735 definitions, 627 Rust regressions and 5350 ledger
obligations.

## M5: numeric data ranges and range facets in the ontology queries

The ontology queries now answer closures and questions that use data ranges of
`owl:real`, `owl:rational` and the twelve subtypes of `xsd:integer`, and
datatype restrictions of every numeric datatype by `xsd:minInclusive`,
`xsd:maxInclusive`, `xsd:minExclusive` and `xsd:maxExclusive` with a numeric
bound of any numeric datatype, inside data restrictions, property ranges,
intersections, unions, complements and enumerations. Every answer is the Direct
Semantics answer under every datatype map that is the OWL 2 map on the
datatypes of `datatypes::literal_value` (`consistent_correct`,
`class_satisfiable_correct`, `subsumed_correct`, `instance_of_correct` and
their prepared forms, whose statements are unchanged).

The encoding orders numbers by cuts of the real line. A cut is a number with a
side, the reals at or above it (closed) or above it (open) (`Rowl.Regions.InCut`).
The context collects the cuts the closure needs (`add_cut_correct`): both cuts
of every numeric literal value; one cut for each range facet, the closed cut of
the bound for `xsd:minInclusive` and `xsd:maxExclusive` and the open cut for the
other two, the upper facets holding outside their cut; and for a subtype the
closed cut of its lower bound and the open cut of its upper bound. `finished`
then adds every number with both cuts to the literal values (`finished_good`).
The new kernel module `regions` orders the cuts exactly, numbers by
`datatypes::compare_values` and a closed cut before the open cut of its number,
by repeated selection of the least cut after the last one (`cut_order_spec`),
and counts the integers that one cut contains and the next does not from the
floors and ceilings of their numbers with the signed digit arithmetic of
`numbers` (`between_spec`), turned into a `usize` up to a cap (`run_size_spec`).
When a datatype restriction or a subtype is in use, every cut gets a class and
the encoding adds (`region_axioms_spec`, `RegionFacts`): the class of the first
cut inside the reals; each cut's class inside the class of the cut before it;
between the two cuts of a number nothing but its literal value's individual;
and, when the integers are in use, for two neighbouring cuts of different
numbers with K integers between them, no integer between them when K is 0, and
at most K of them at any element along a role `U`, which includes every data
property's role, when 0 < K and K is below the capacity (`GapFact`; a run of
as many integers as the capacity or more gets no axiom, and the kernel counts
no further than one past the capacity). A
subtype becomes the integers in its lower bound's cut and outside its upper
bound's cut, and a facet its cut's class or that class's complement
(`kind_range_meaning`, `facet_class_meaning`): `NodeValue` now asks that each
cut's class hold at a data node exactly when the node's value is a real in the
cut.

The capacity bounds the counts of the data restrictions of the closure and its
questions. Each data restriction counts the values that decide it (an
existential, universal or value restriction 1, a minimum n, a maximum n + 1,
an exact restriction 2n + 1, `atomCount`), and `class_count` and `items_count`
add them up, capped at `usize::MAX / 16` (`class_count_spec`,
`items_count_spec`). `prepare` leaves room for 64 values in questions
(`QUESTION_ROOM`); a question to a prepared closure that counts more gets no
answer, and the direct queries make room for their own question.

An OWL model lifts to a model of the encoding as before, now with each value in
the cut classes of its real (`node_cut`) and every element related along `U` to
the values of the context's data properties at it, so a run of K integers has
at most K of them at any element (`lifted_regions`). Conversely, a model of the
encoding gives an OWL model (`sound`) in which each data node that witnesses an
element's data restriction takes a value of its region (`regionOf`): the reals
of its level, the least of the integers, the decimals and the rationals whose
class in use holds at it or else the irrational numbers (`levelOf`,
`number_profile`), in the interval between the cuts its cut classes place it
(`positionOf`, `position_cut`, `regionSet`). Every region is infinite
(`Rowl.DataReals.level_infinite`, `integers_above`, `integers_below`,
`region_cases`) but a bounded run of integers between cuts of different
numbers, which has exactly the kernel's count of members (`run_ncard`). A
numeric literal value lies in no interval but its own point (`literal_outside`),
and a point holds no data node but its literal value's individual
(`not_point`), so the values of the other data nodes are no literal values
(`region_not_literal`). An element's data nodes in a run are numbered among its
peers in that run (`peers`), and the numbers fit (`peers_bound`): by the axiom
on the run when it has fewer integers than the capacity, since every successor
along a data property's role is one along `U` (`successor_super`), and
otherwise because an element has at most as many witnesses as the counts of the
data restrictions (`witness_list_length`). Distinct data nodes of an element
therefore get distinct values (`nodeValue_injective`) that stand for them
(`value_node`, `place_node`), and the OWL interpretation satisfies the closure
whenever the interpretation of the encoding satisfies its encoding
(`sound_satisfies`), for every list of data restrictions that covers the
closure's and counts at most the capacity.

Statements that changed: `encode` takes the capacity; `encode_meaning` asks
that it be below `usize::MAX / 16` and gives the order of the cuts; `Frame` has
the facts of the cuts; `NodeValue`, `RangeFrame` and `Placed` take the
embedding `num` of the reals among the values; `sound_satisfies` and
`sound_class` ask that the data restrictions count at most the capacity
(`Setting` gathers what a model of the encoding brings); `DataPrepared` records
the capacity and the room; `known_plain`, `encoded_model` and `lifted_model`
take the capacity. The DataSound lemmas on the regions of the five datatypes
(`number_kind`, `text_kind`, `tagged_kind`, `region_profile` and their helpers)
are replaced by `real_space`, `text_space`, `tagged_space`, `number_profile`
and `text_profile`.

The regressions (`tests/numeric_ranges.rs`) check, among others, that a dose
above a daily maximum `xsd:decimal[<= 4000]` makes the records inconsistent,
that a value of `"8001/2"^^owl:rational` triggers an overdose class defined by
`xsd:decimal[> 4000]`, that an element can have 256 values of `xsd:byte` but not
300, that `owl:real[> 0, < 1]` without `owl:rational` is satisfiable while
`xsd:integer[> 0, < 1]` is not, that every integer subtype contains its bounds
and nothing beyond them, and that a prepared closure answers a question with 10
values of `xsd:unsignedByte` but leaves one with 100 to the direct query. The
ledger entries of the sixteen numeric datatypes and the four range facets are
verified. The cross-cutting facet entries (DatatypeFacetApplicability,
ExactLexicalInterpretation, ValueEquality, CrossDatatypeOverlap,
FiniteCardinality, AtLeastN, ConstraintSatisfiability, DomainComplement) are
implemented: their scope says that the numeric datatypes, `xsd:string`,
`rdf:PlainLiteral` and `xsd:boolean` are done and the other datatypes are not.
The other facets, facets with bounds that are no numbers, data ranges of the
other datatypes, datatype definitions and keys still get no answer.

Closures without datatype restrictions and integer subtypes get no cut classes
and no region axioms, so their encoding is as before. The eleven regressions of
`tests/numeric_ranges.rs` take 7.2 s together in a debug build, most of it for
the 256 and 300 values of `xsd:byte`. Each distinct numeric literal value of a
closure that orders numbers adds two cuts, and a value's node is in the classes
of all cuts below it, so the tableau grows with the square of the number of
distinct numeric values; the next block measures this on a generated
ontology.

This block adds 219 public theorems and 51 definitions and removes 8 theorems
and 1 definition of the former regions. Totals are 5368 audited theorems, 1785
definitions, 638 Rust regressions and 5561 ledger obligations.

## Performance: cuts only at the bounds of facets and subtypes

The region encoding of the previous block gave every numeric literal value
its two cuts. With n distinct numeric values a closure had about 2n cuts, each
value's individual was in the classes of all cuts below it, every value added
an axiom with a nominal, and the kernel ordered the cuts by repeated selection,
so reasoning grew much faster than n. Now only the bounds of facets and of
integer subtypes are cuts: literals add none (`add_literal_good`). Each
numeric literal value's individual is asserted in the class of every cut that
contains its number and outside the others (`cut_memberships_spec`,
`CutFact`), with the membership decided exactly by the new `regions::in_cut`
(`in_cut_correct`). A literal value can therefore lie inside a run of integers
between two cuts, and the axiom on the run counts the integers that are no
literal values (`freeCount`, from `run_count_spec` and `run_literals_spec`):
when there are none, every integer node of the run is one of the run's
literal values' individuals, and when there are fewer than the capacity, at
most that many other integer nodes are at any element along `U` (`GapFact`,
`gap_axiom_spec`; the kernel declines when the literal values of a run and the
capacity together reach `usize::MAX / 16`). The lifted model of an OWL model
satisfies these axioms because the literal values of a run are distinct
integers of the run (`named_card`, `all_named`, `lifted_regions`), and the
model made from a model of the encoding takes the values of its number regions
outside the numbers of the literal values (`literalReals`, `regionSet`), which
leaves exactly the free integers of a bounded run (`free_reals`, `free_card`,
`run_count`) and infinitely many values in every other region (`region_cases`).
Points of facets keep their literal values, as before. Statements that
changed: `CutFact`, `GapFact`, `encode_meaning`'s `ValuesFit` (every numeric
literal value short enough to compare) in place of `ValuesCut`, and the
DataSound region definitions, which now take the set of literal reals. The
regression `literal_values_take_integers_of_a_run` checks runs whose integers
are partly or wholly literal values.

On the medication-dose ontology of `tools/bench/gen_numeric.py` (n
prescriptions of five drugs, each with an `xsd:decimal` daily dose and an
`xsd:integer` age, against maximum doses, age groups and dose bands defined by
range facets; release builds), deciding consistency (`rowl check`) took 23.0 s
for 10 prescriptions before and 0.04 s now, more than 120 s for 20 before and
0.14 s now, and now 1.1 s for 50 and 7.9 s for 100. Listing the overdoses
(`rowl instances`, one instance query per prescription) took 224.6 s for 10
before and 0.27 s now, and now 2.6 s for 20 and 61.5 s for 50; for 100 it
takes more than 300 s, because every instance query runs the completion forest
over all prescriptions again, and copying the forest at its branch points
dominates. The regressions of `tests/numeric_ranges.rs` take 11.7 s in a debug
build, most of it for the 256 and 300 values of `xsd:byte`.

This block adds 25 public theorems and 9 definitions and removes 4 theorems and
1 definition. Totals are 5389 audited theorems, 1793 definitions, 639 Rust
regressions and 5582 ledger obligations.

## M5: numeric data in the examples, the CLI and the README

`examples/medication-dose.ofn` checks paracetamol prescriptions against a
daily maximum: a dose above 4000 mg, or above 2000 mg for a child under 12
(`DataSomeValuesFrom(:patientAgeYears xsd:integer[< 12])`), is a dose alert,
and one dose is written `"8001/2"^^owl:rational`. The README shows the alerts
that `rowl instances` lists from the file's bytes, and
`crates/rowl/tests/reasoner.rs` checks them, the child, the classification of
the example and that a hard maximum `DataAllValuesFrom(:dailyDoseMg
xsd:decimal[<= 4000])` makes the records inconsistent. The README's table and
`rowl status` now name the numeric datatypes and the four range facets. The
`Reasoner`, the command-line tool and the Python package needed no change:
they pass the data ranges of the read document to the same verified queries.
The medication-dose ontologies of the previous block's measurements come from
the benchmark generator `gen_numeric.py` of the shared `tools/bench`
(`python3 gen_numeric.py N OUT` writes `OUT.ofn`).

This block adds no theorems. Totals are 5389 audited theorems, 1793
definitions, 640 Rust regressions and 5582 ledger obligations.

## M5: keys together with the numeric data ranges

Merging the numeric datatypes into the keys branch: a closure with keys is
encoded by `key_ontology` on top of the data encoding with a capacity, as the
other closures are, so keys and the numeric data ranges and range facets work
together. `key_ontology::prepare` now takes the room for a question's data
restrictions and finishes the context again after adding the keys' class
expressions and properties (`finished`, so the truth values and the numbers of
the cuts of the keys' data ranges are literal values too), and its capacity
counts the data restrictions of the keys' class expressions as well
(`keys_count`, `keys_count_spec`), since `HasKey` axioms count none in
`items_count`. `Prepared::Keyed` keeps the room, and the prepared queries of a
closure with keys decline a question that counts more than the room, as for the
other closures.

`KeyEncoding.encode_meaning` passes on what the data encoding's
`encode_meaning` now gives (the cuts, their order and the frame for the
capacity); `KeyModels` builds `liftedN` on the lifted interpretation with its
reals (`liftedN_frame` carries the cut classes, the role above the data
properties and the region facts over, `liftedN_cut_class`, `liftedN_super`)
and `keyedSound` on `sound` with the order of the cuts (`keyedSound_simulates`
and `keyedSound_placed` from a `Setting` and a count of the data restrictions
that the capacity bounds). `DataPrepared` of a keyed closure records a capacity
that bounds the closure's data restrictions, its keys' and the room
(`key_prepare_correct`, `key_prepare_with_correct`). A regression test asks
about keys whose class is a numeric range (orders with a dose of at least 500
identified by their prescription): two such orders with one prescription are
equal, a stated inequality makes the closure inconsistent, and an order with a
lower dose is not identified.

The ledger and scope texts now say that keys with a data property, not keys,
get no answer. Data-property keys remain undone: they need the values that the
model made from a model of the encoding gives the named elements to differ
unless their data nodes are the same literal value's individual, which now must
hold for the values chosen in the regions of `DataSound` too, and every value
of a finite run of integers must then be a literal value's individual (or such
keys declined).

This block adds 9 public theorems, no definitions and 1 Rust regression.
Totals are 5398 audited theorems, 1793 definitions, 641 Rust regressions and
5591 ledger obligations.

## M3: reasoning over RDF/XML documents

The verified XML and RDF/XML readers now feed the reasoner. The catalog reader
`import_catalog::read_source` gains the format `RdfXml(base)`: `read_rdfxml`
reads a document with `rdfxml::read_with_limits` under `rdfxml_limits` (an
entity expansion budget and term limit of 2^24 and an item limit of
`usize::MAX / 2`), after checking that the byte length plus the budget fits in
`usize` (`TooLong` otherwise), and maps the graph with the verified reverse RDF
mapping. `ReadAs` and `RejectedAs` say what it returns, independently of the
Rust code: an ontology that the mapping reads from a graph whose statements are
those the RDF/XML grammar (`RdfXmlGrammar.Graph`) determines for the element
tree the XML grammar (`XmlGrammar.Read`) reads from the bytes, or the XML
error exactly when the XML grammar reads no tree, the RDF/XML error exactly when
the tree has no graph within the limits, `Graph` when the mapping reads none,
and `TooLong` exactly for documents too long for the budget.
`read_source_correct` keeps its statement and now covers the RDF/XML arm,
composing `RdfXml.read_total` and `RdfXml.read_correct`.

`Reasoner::from_rdfxml` and `from_rdfxml_with_base` read a document through the
same `read_source`, and catalogs take `Syntax::RdfXml(base)`, so import closures
can mix RDF/XML with the other syntaxes. The CLI reads `.owl` and `.rdf` files as
RDF/XML, also in `--imports` directories, and resolves the relative IRIs of
Turtle and RDF/XML files against the file's `file:` IRI (percent-encoded), as a
document without `@base` or `xml:base` expects. The C interface adds
`rowl_reasoner_from_rdfxml` and `rowl_reasoner_from_turtle_with_base` (both with
a base IRI) and the catalog syntax code `ROWL_SYNTAX_RDFXML`; the Python package
reads `.owl` and `.rdf` files, and `Reasoner(..., syntax="rdfxml", base=...)`.
Load errors name the XML or RDF/XML fault in words.

Regressions: `examples/maintenance.owl` and `examples/medication-safety.owl`
read to the graphs of their N-Triples versions up to blank-node renaming, and
answer every query as those do; a relative IRI resolves against a supplied base
and fails without one; malformed XML, `parseType="Literal"` and undeclared
graphs give their distinct errors; an import closure of a Functional Syntax
document and an RDF/XML vocabulary answers instance questions across them; the
CLI and Python read `.owl` files; every example, `.ttl` and `.owl` included, is
OWL 2 DL. The W3C RDF/XML suite (the ignored test
`official_w3c_rdfxml_cases`, run with `ROWL_RDFXML_SUITE_DIR`) passes every
evaluation and negative case except the three that use XML literals.

The XML reader decodes and scans by recursion once per character, which the
compiler does not turn into loops, so it needs about 160 bytes of stack per
byte of input. The reasoner's kernel stack grows from 1 GiB to 4 GiB on 64-bit
targets (committed only as used), which reads RDF/XML documents of about
25 MB. Classifying the generated 20 000-class EL ontology takes 2.1 s from its
7.9 MB RDF/XML form (1.3 GB peak, mostly stack), against 0.65 s from N-Triples
and 0.54 s from Turtle, with identical answers. Rewriting the per-character
recursions of the readers as loops, so that the stack no longer grows with the
input, is the next step for large documents.

This block adds no public theorems or definitions. Totals are 5398 audited
theorems, 1793 definitions, 649 Rust regressions and 5591 ledger obligations.

## Performance: XML decoding in constant stack

`xml::decode_from`, which decodes a document into code points, recursed once per
character; the compiler does not turn that recursion into a loop, so reading an
RDF/XML document took about 160 bytes of stack per byte. It is now a Rust
`loop`, which Aeneas extracts as the recursive `xml.decode_from_loop` with the
same body, so its proof carries over unchanged (`decode_from_loop_spec`) and
`decode_from_spec` and every theorem above it keep their statements. Element
content still recurses once per sibling element, about 1.6 KB of stack each.

Reading the 7.9 MB RDF/XML form of the generated 20 000-class EL ontology now
needs less than 64 MB of stack instead of more than 1 GiB; classifying it takes
1.33 s and 334 MB instead of 2.13 s and 1.3 GB, and the 4 GiB kernel stack
reads documents of a few hundred MB.

This block adds no public theorems or definitions. Totals are 5398 audited
theorems, 1793 definitions, 649 Rust regressions and 5591 ledger obligations.

## Performance: one pass over the requirements in the tableaux

Both tableaux looked for missing work node by node: for every node,
`missing_at` scanned all requirements of all individuals to find the few at
that node, so each search step cost the number of nodes times the number of
requirements. A profile of a consistency check of a generated medication-dose
ontology with 100 prescriptions put 91% of the time in
`forest::missing_requirement`. Now `missing_requirement` checks every
requirement once, at the node its individual is merged into (`unmet`), and
`missing_node` falls back to the node-by-node search (`missing_local`) only for
the local needs: the TBox concept, the unfoldings and the seeds. The same change
applies to the completion graph of `completion`. `missing_requirement_correct`,
`missing_at_correct` (now about `LocalNeeds`) and `missing_node_correct` are
restated for the new functions in `ForestSearch` and `CompletionSearch`;
`missing_node_correct` gives the same guarantee as before, so `next_step` and
every theorem above it keep their statements.

The consistency check of the dose ontology with 100 prescriptions takes 0.55 s
instead of 7.9 s; listing its 11 overdoses takes 72 s instead of more than
300 s, since every instance question still runs its own tableau.

This block adds no public theorems or definitions. Totals are 5398 audited
theorems, 1793 definitions, 649 Rust regressions and 5591 ledger obligations.

## Performance: full IRIs read up to their first `>`

Functional Syntax documents that write every name as a full IRI `<…>` were read
about 240 times slower than the same documents with prefixed names: the lexer
matched the full-IRI grammar at every token start and tried every endpoint.
`names::full_iri` now finds the greatest full-IRI endpoint directly. No RFC 3987
IRI contains `>` (`noGt_iri`, by induction over the IRI grammar), and every byte
of a multi-byte UTF-8 unit is at least 128, so a full-IRI word from a `<` ends
just after the first `>` byte. The scanner looks for that byte (`gt_from`) and
validates the bytes before it once with `iri::validate_iri`.
`full_iri_correct` proves that the answer is the greatest candidate endpoint of
the independent full-IRI language `<` IRI `>`, or no endpoint when there is
none. `functional::ascii_name` asks it for the `FullIri` terminal before the
grammar matcher, and `ascii_name_correct` gains the corresponding case, so
`longest_valid_eq` and every lexer theorem above it keep their statements. The
regression `full_iri_scanner_agrees_with_the_grammar` compares the scanner with
the grammar matcher on 3000 generated token-shaped texts.

Classifying the generated 5000-class EL ontology written with full IRIs takes
0.40 s instead of 93 s, the same as with prefixed names (0.38 s), with the same
answers.

This block adds one public theorem (`Rowl.Names.full_iri_correct`). Totals are
5399 audited theorems, 1793 definitions, 650 Rust regressions and 5592 ledger
obligations.

## Performance: edges before the TBox concept in the tableaux

Both tableaux searched for work in a fixed order that gave every node its TBox
concept and unfoldings before any universal restriction was passed along an
edge. With the TBox concept every node branches on its disjunctions, so all
nodes made their choices before any edge was used. A choice that clashes only
with a neighbour, such as `∀age.¬(<12)` at a prescription for a child, was then
found to fail only after every later node had branched, and backjumping to it
discarded all their work: checking the consistency of a generated
medication-dose ontology took 0.54 s for 100 prescriptions and 40 s for 300.

The search now runs in three parts (`missing_work` in both `completion` and
`forest`): the requirements of the individuals, then what the edges require of
their ends (links and tree edges, and in the forest added edges and loops), and
only then the TBox concept, the unfoldings and the seeds of the nodes. What the
choices at one node require of its neighbours is added, and a clash they cause
is found, before the next node branches. `missing_work_correct` replaces
`missing_node_correct` in `CompletionSearch` and `ForestSearch`, with the same
guarantee for the combined search: what it returns is something a node lacks
and needs, and when it returns nothing every node has what it needs and every
edge is satisfied. `next_step_correct` keeps its statement, so the tableaux and
every theorem above them keep theirs.

| Consistency check | before | after |
| --- | --- | --- |
| medication doses, 100 prescriptions (forest) | 0.54 s | 0.23 s |
| medication doses, 300 prescriptions (forest) | 40.4 s | 1.58 s |
| prescriptions with age and dose groups, 200 records (completion graph) | 1.32 s | 0.34 s |
| the same, 400 records | 11.1 s | 1.60 s |
| the same, 800 records | 101.8 s | 5.68 s |

Listing the 11 overdoses among 100 prescriptions takes 53 s instead of 72 s,
and the 37 instances among the 100 records of the second ontology 26 s instead
of 50 s: every instance question still runs a tableau over the whole ABox.

This block adds no public theorems or definitions. Totals are 5399 audited
theorems, 1793 definitions, 650 Rust regressions and 5592 ledger obligations.

## Glue: safer instance listing

A review of the README found three gaps in the unverified `rowl instances`
command, which asks the verified instance query about each named individual:
it printed nothing and exited successfully when no answer was known, it listed
every individual of an inconsistent ontology without saying why, and it never
asked about individuals that occur only in class expressions
(`ObjectOneOf`, `ObjectHasValue`). `Reasoner::individuals` now includes those
individuals, and `instances` names every individual whose answer is unknown
and then exits with status 1, and on an inconsistent ontology lists nothing and
exits with status 1. The `alc_ontology` example now asks the ontology queries
of `data_ontology`, which answer it at once instead of in about two minutes,
and stale statements in status.md, formats.md and the Python documentation
(RDF/XML reading, the range facets, reading times) are corrected.

This block adds no theorems or definitions. Totals are 5399 audited theorems,
1793 definitions, 654 Rust regressions and 5592 ledger obligations.

## Performance: instance questions about one component

Every instance question ran a tableau over the whole ABox, so listing the
instances of a class over n individuals took n tableaux of size n: 53 s for the
11 overdoses among 100 medication-dose prescriptions. Independent records do
not need each other: a model of the assertions about some individuals and a
model of the others combine into a model of both whenever they share no
individual and the other axioms name no individual.

`Rowl.Partition` proves this for the OWL 2 Direct Semantics. Call an axiom other
than an assertion plain when it names no individual (no `ObjectOneOf` or
`ObjectHasValue`), uses neither top property, defines no datatype, gives a key
an object property, and has only standard data: datatypes that the datatype map
supports or `rdfs:Literal`, literals of the vocabulary, and facets of the
vocabulary whose facet values are datatype values (`Standard`). The disjoint
union of two interpretations (`join`) puts the individuals of one part on the
left and the others on the right; its data domain is the sum of the two data
domains, with every datatype value of the right carried to the embedding of the
same value on the left (`carry`), so literals, supported datatypes and range
facets mean the same on both sides. `join_interpretation` proves it an
interpretation for the vocabulary; `side_class` proves that a plain class
expression means the same at an element of either side as in its own
interpretation; `join_plain`, `join_left_assertion` and `join_right_assertion`
prove that it satisfies the plain axioms that both interpretations satisfy and
each side's assertions. `instance_part` concludes: when the closure has a model
and its assertions fall into a part and a rest that share no individual, an
instance question about an individual that the rest does not name, with a plain
class expression without individuals, has the same answer for the part as for
the closure. The part may hold copies of the closure's axioms and the rest
declarations and annotation axioms.

`components::component_closure` checks that every axiom of the closure is plain,
a plain assertion or without meaning (`plain_items_spec`), finds the component
of the named individual in rounds over the assertions, checks that it holds the
individual and that every assertion that names one of its individuals names
only its individuals (`closed_spec`), and copies the plain axioms and the
assertions of the component without their annotations (`select_spec`,
`copy_axiom_spec`). `component_closure_correct` gives the result the
conditions of `instance_part`, and `part_instance_correct` composes them: for
every datatype map that is the OWL 2 map on the datatypes of `datatypes` and
every vocabulary, the instance question has the same answer for the part.
`Reasoner::instance_of` asks the part when the closure is consistent and the
class expression passes `plain_question`, and the whole closure otherwise; it
keeps splitting when the first part is less than half of the closure. The
consistency answer is now computed once and kept.

| Listing instances | before | after |
| --- | --- | --- |
| 11 overdoses among 100 medication-dose prescriptions | 53 s | 0.41 s |
| 37 overdoses among 100 records with age and dose groups | 26 s | 0.61 s |

Listing the 43 overdoses among 300 prescriptions takes 2.28 s, of which the
one consistency check of the whole closure takes 1.58 s. The regression
`parts_answer_like_the_whole_closure` compares, for every
individual with a part and every named class of four ontologies, the answer of
the part with the answer of the whole closure.

This block adds 28 public theorems (11 in `Rowl.Partition`, 17 in
`Rowl.Components`) and 16 definitions. Totals are 5427 audited theorems, 1809
definitions, 657 Rust regressions and 5620 ledger obligations.
