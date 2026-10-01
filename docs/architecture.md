# Accepted architecture and implementation contract

## Scope

Full OWL 2 DL with the 2012 second-edition Direct Semantics; Functional Syntax
and standard RDF graph/dataset inputs; Rust library and CLI. The user expanded
the format scope to RDF/XML, Turtle, N-Triples, N-Quads, TriG and JSON-LD
read/export, plus RDFa read, using the finalized versions in [formats.md](formats.md).
Datasets require explicit graph selection and preserve all other graphs.
This added scope remains planned; storing document bytes does not parse them.
Queries: ontology consistency, class
satisfiability, classification, instance checking and named fact entailment.
No general graph query language is promised for v0.1.

Proof scope begins at input bytes and includes parsing, RDF-to-structural
mapping, canonical declaration handling, import closure, DL validation,
semantic transformations, datatypes, the decision procedure and query
reductions. Every semantic dependency is either proved or explicitly part of
the accepted toolchain/primitive-model trusted computing base. An unverified
parser or external solver cannot silently become an ontology axiom.

Immutable caller-supplied catalogs map document IRIs to bytes. Import cycles
must terminate, missing imports are errors, and v0.1 does not fetch documents
from the network. Blank-node identity is scoped correctly per ontology.
Headerless imported RDF documents must follow the mapping's include behavior.

Single-threaded deterministic in-memory snapshots, full recomputation after
edits, explicit cancellation/resource results and replayable derivation traces.
Persistence, bindings, incremental reasoning and parallel execution come later.
The core is owned by this project; I/O adapters may be reused after licensing
and proof-boundary review. No performance promise or release date is fixed.

## Pipeline and boundaries

1. Bytes and immutable catalog → RDF graph/dataset, explicit graph selection,
   shared canonical RDF-to-OWL mapping, structural ontology and provenance.
   Functional Syntax enters the structural stage directly. Proved serializers
   preserve graph/dataset meaning up to blank-node isomorphism or return a typed
   representability error; no graph is silently discarded.
2. Complete axiom closure → OWL 2 DL validation, including global restrictions.
3. Validated ontology → normalized/prepared state, role automata and data constraints.
4. Query → a semantics-preserving satisfiability reduction.
5. SROIQ-style tableau and datatype solver → a decision and replayable evidence.
6. Facade → typed answers; CLI only reads bytes and renders results.

The frontend and kernel crates have no unsafe code. `ValidatedOntology` will
mean structurally/global-restriction valid, not logically consistent. Handles
are snapshot-owned. IRIs, typed entity occurrences, structural expression
identity and logical individual equality are separate notions. Punning does
not make an entity's interpretations equal.

Planned public outcomes distinguish `Consistent`, `Inconsistent`, `Entailed`,
`NotEntailed` and `EntailedByInconsistency`. Invalid input/query, missing import,
cancellation and resource exhaustion are separate errors. Classical explosion
is surfaced explicitly with inconsistency evidence. `NotEntailed` does not
assert a negative fact.

## Semantic invariants

- Open-world semantics: missing facts do not imply negative facts.
- No unique-name assumption: different IRIs can denote the same individual.
- An unsatisfiable class can be empty while its ontology remains consistent.
- Existentials require witnesses, not necessarily named individuals.
- Tableau blocking is not individual equality; complete branches may represent
  infinite models through unravelling. One open branch does not prove entailment.
- Named input individuals, input anonymous individuals and internal witnesses
  remain distinct categories. OWL keys use NAMED restrictions; internal witnesses
  and nominals must not accidentally acquire named status.
- A class-satisfiability reduction cannot indiscriminately add a fresh *named*
  individual: keys can change the answer. Use a proved un-NAMED witness reduction.
- Literal lexical identity differs from datatype value equality. Data complements
  range over the data domain, not merely the base datatype's value space.
- Datatype cardinality/inequality constraints require exact reasoning, including
  finite spaces. Generic Rust regex behavior is not XML Schema regex semantics.
- Search priorities, fairness, merge/prune/restore and blocking conditions must
  agree with the selected calculus and its completeness/termination arguments.
- Fuel bounds one run; it does not establish eventual termination of the
  decision procedure. Prove both semantic correctness and eventual decision.

## Milestones

| Milestone | Deliverable | Exit criterion |
| --- | --- | --- |
| M0 | Scope, requirement inventory, proof/TCB contract | Every constructor/axiom family and cross-cutting obligation tracked |
| M1 | Actual Rust-to-Lean feasibility probes | Small procedure proved sound/complete/terminating; mutation, vector, branching and parser/arithmetic probes audited separately |
| M2 | Full typed structural model and independent formal semantics | All syntax and Direct Semantics constructs represented |
| M3 | Verified frontend, catalogs and standard formats | Byte parsing, RDF datasets/selection, mapping, canonical imports, serialization laws and diagnostics proved |
| M4 | DL validation, normalization and role preprocessing | Validation and model-preserving transformations proved |
| M5 | Normative datatypes and constraint solver | Lexical/value/facet/cardinality/solver correctness proved |
| M6 | SROIQ tableau | Integrated soundness, completeness and termination, including rule interactions |
| M7 | Full OWL integration | Keys, NAMED, anonymous individuals, built-ins, punning and datatypes covered |
| M8 | Queries and evidence | Reductions and trace replay proved; resource outcomes implemented |
| M9 | Byte-to-answer composition and release | Full proof coverage, meaningful tests and reproducible exact-source verification |

The first M1 probe is a finite Boolean class language over two atoms. It tests
recursive owned expressions, shared borrows, short-circuit evaluation, branching,
witness results, mutable search-state transitions, a terminating loop and actual
extraction. M1 now also proves bounded-index Vec mutation, ASCII digit recognition,
recursive immutable catalog lookup and exact unary-natural addition. These are
feasibility probes: they establish neither a full parser/import resolver nor the
final arithmetic representation or tableau data structures. M1 is complete at
that deliberately limited scope.

M2 represents all standard structural constructors and defines their independent
declarative semantics over the actual extracted Rust types. Nonempty/minimum
written arities and ontology/version header relationships are encoded in types.
The raw AST still needs lexical validation, duplicate-free unordered associations,
structural equivalence, complete imports and DL validation in M3–M4. All standard
data ranges are unary; the specification's nonstandard n-ary extension hook is
outside the chosen OWL 2 DL scope. Datatype maps are mathematical parameters;
implementing/proving the normative map and solver remains M5.

## Release gates

No `sorry`, admitted ontology claims, custom semantic axioms or unsupported
constructs in the release proof scope. Audit each exported theorem's assumptions;
pin tools and source-to-generated-file linkage. Every inventory obligation must
have a concrete implementation, theorem and regression case, including their
interactions. Resolve differential-test discrepancies against independent
reasoners rather than treating either implementation as an oracle. Test evidence
alone is not a correctness proof. No fragments may be relabeled as full v0.1.

## Primary references

- [Direct Semantics, 2012](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/)
- [Structural Specification, 2012](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/)
- [Mapping to RDF, 2012](https://www.w3.org/TR/2012/REC-owl2-mapping-to-rdf-20121211/)
- [Conformance, 2012](https://www.w3.org/TR/2012/REC-owl2-conformance-20121211/)
- [OWL errata](https://www.w3.org/2007/OWL/wiki/Errata) (snapshot must be pinned before release)
- [RDF/XML edition referenced by OWL](https://www.w3.org/TR/2004/REC-rdf-syntax-grammar-20040210/)
- [XML Schema Datatypes](https://www.w3.org/TR/xmlschema-2/)
- [RDF Plain Literal](https://www.w3.org/TR/rdf-plain-literal/)
- [The Even More Irresistible SROIQ, Horrocks/Kutz/Sattler](https://cdn.aaai.org/KR/2006/KR06-009.pdf)
- [Datatypes algorithm, Motik/Horrocks](https://www.cs.ox.ac.uk/boris.motik/pubs/mh08datatypes.pdf)
- [Aeneas](https://github.com/AeneasVerif/aeneas)

The published SROIQ calculus is a starting point; OWL keys, datatypes, frontend
and query reductions still require integration proofs. Pin referenced standard
editions and normative dependencies; do not silently adopt newer RDF semantics.


M3 and M4 currently have verified executable components: symbol-indexed document
closure, strict UTF-8/XML text decoding and reachable-source composition,
raw RDF positional terms/datasets and explicit lossless graph selection,
explicit entity/declaration collection from the full raw OWL AST, exact byte
IRI symbols and a composed raw-ontology declaration checker with implicit
built-in roles, reserved-vocabulary/header checking, inverse assertion
canonicalization and ordered universal subclass constraint preparation. These do
not satisfy the full M3/M4 exit criteria. See `m3-m4-progress.md` for exact proof
contracts, including the still-unproved parser-derived metadata, base/prefix and ontology IRI integration,
literal/facet validity and global DL restriction links.


## Duplicate-disjointness compatibility decision

The user delegated the reported duplicate-disjointness ambiguity decision, and
ROWL adopts the documented correction proposed in the W3C discussion. Structural
validation must require pairwise structurally distinct operands for
DisjointClasses, DisjointObjectProperties, DisjointDataProperties,
DifferentIndividuals, and the member classes after the defined class in
DisjointUnion. Raw syntax retains occurrences until that check; dropping a
repeated operand before validation is forbidden. RDF `x owl:disjointWith x`
maps to `SubClassOf(CE(x), owl:Nothing)`, preserving the empty-class meaning.
This conversion needs its own model-equivalence proof in the RDF-to-OWL mapper.

This is an explicit compatibility interpretation, not an amendment to the 2012
Recommendation. The [W3C errata report](https://www.w3.org/2001/sw/wiki/OWL_Errata)
states that reported proposals did not amend that Recommendation. The
[April 2014 correction proposal](https://lists.w3.org/Archives/Public/public-owl-comments/2014Apr/0000.html)
and [subsequent structural-validity discussion](https://lists.w3.org/Archives/Public/public-owl-comments/2014Apr/0001.html)
explain the duplicate/set inconsistency. Release documentation and conformance
reports must identify this choice. Duplicate validation is now implemented and proved by `arity::check_arities`.
The RDF conversion is not implemented or proved yet; that separate obligation
and the full-language release target are unchanged.

## Anonymous occurrence and graph interpretation

For the 2012 [Structural Specification §11.2](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#The_Restrictions_on_the_Axiom_Closure), ROWL follows the literal
whole-axiom anonymous-occurrence prohibition, including recursively nested
annotations on the four specified axiom types. Other types permit anonymous
annotation values. Anonymous scope/label byte keys identify structural input
occurrences after standardization apart; they do not imply distinct denotations.
A self assertion is a loop and cannot belong to a forest. Repeated endpoint
pairs form a single undirected graph edge; the separate assertion-multiplicity
rule must count structurally distinct annotated axioms as set members.

The named-boundary rule requires each anonymous component to have some vertex
incident to at most one positive assertion with a named endpoint. ROWL implements
and proves that normative rule. The adjacent Francis/family illustration gives
its single anonymous vertex four such assertions, apparently contradicting the
literal condition. That informative illustration does not change the release
contract. No applicable correction was found in the published
[OWL errata](https://www.w3.org/2001/sw/wiki/OWL_Errata) during this review.
The boundary decision is checked over every component, including the
automatically qualifying isolated occurrences. Distinct-assertion counting is
checked from raw occurrences with recursive annotation-set equivalence; the
positional, forest and multiplicity components do not depend on that discrepancy.
The composed checker also has a totality/acceptance proof for all anonymous
restrictions together, with original evidence and deterministic failure priority.
Multiplicity validation precedes inverse-assertion lowering: logical equivalence
does not imply structural axiom equality.


### Datatype definition identity and availability

The 2012 Structural Specification's [structural equivalence rules](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Structural_Equivalence)
apply recursively to data-range member associations, facet/literal associations
and annotations. ROWL compares those sets while retaining constructor kind,
nesting, exact IRI identity and literal spelling. Datatype definitions differing
in annotations are structurally distinct axioms even if their meanings coincide.
The availability validator uses this identity on the original raw closure,
including before any semantic normalization.

The [axiom-closure restrictions](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#The_Restrictions_on_the_Axiom_Closure)
require custom datatypes to have one definition and prohibit redefining predefined
names. ROWL's definition-availability operation checks precisely those conditions
on every explicit datatype occurrence; it does not accept a caller's occurrence
summary. Equivalent raw copies count as the same axiom, including reordered
recursive associations. Datatype dependency acyclicity is a separate gate.
The [custom datatype restrictions](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Datatype_Definitions)
on literal datatypes and restriction bases, the normative datatype map and facet
membership retain their separate implementation/proof requirements. No success
from this operation alone is a claim of full OWL 2 DL validity.


### Datatype dependency order

The [normative datatype dependency order](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#The_Restrictions_on_the_Axiom_Closure)
is checked from the actual typed datatype occurrences of every defining data
range. Every such occurrence precedes the defined datatype. Literal datatypes
in enumerations and facet values contribute edges; enclosing axiom annotations
and untyped facet IRIs do not occur in the range's typed datatype positions.

ROWL's directed checker uses finite edge removal rather than heuristic fuel.
A new edge closes a cycle exactly when its target can already reach its source.
Duplicate edges and directed diamonds remain valid. The proof distinguishes
reflexive reachability from nonempty paths, proves that cycle freedom yields
exactly a containing strict partial order, and proves the carrier agrees with
all datatype names actually present in Ax. Success has a mathematical order
witness; the current Rust API returns Acyclic rather than a materialized order.
Rejection retains an original dependency pair with a proved reverse path.

The composite definition-rule validator proves both availability/uniqueness and
acyclic ordering, with availability diagnostics taking priority. Custom datatype
position restrictions and concrete datatype lexical/facet/value validation stay
separate. The current directed search permits exponential time, consistent with
the prototype's correctness-first scope; efficient closure and physical resource
handling retain their own implementation/proof obligations.


### Defined datatype positions and annotation context

The [datatype definition position restrictions](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Datatype_Definitions)
are decided from actual defining axioms, rather than treating all unfamiliar
names as defined. Defined names may occur as data ranges, while their empty
lexical spaces and unsupported facets forbid literal datatype and restriction-
base positions. The full raw AST traversal covers recursive annotations too.
Literal lexical correctness and general facet membership remain separate checks.

The supplied raw ontology's axiom vector is the complete definition context.
Its supplied ontology annotations are checked before axiom positions. Imported
ontology annotations must also be checked against this complete context; using
only each import's local definitions would miss imported custom names. Canonical
assembly will retain and verify that context as part of the full frontend proof.
The current positional API does not claim unsupplied import annotations were checked.

The composite structural datatype operation checks definition rules before
positions, returns original failure objects, and certifies preceding stages.
Its proved conjunction acceptance covers these structural rules without assuming
a concrete lexical/facet/value-space solver or complete DL validity.


Class structural identity must expand cardinality omission defaults before
comparison: absent object fillers are the exact named owl:Thing and absent data
fillers the exact named rdfs:Literal. The proved class comparator now implements
this with recursive set associations and retains all constructors/nesting. Future
canonicalization and distinct-operand checks must use this relation rather than
raw field equality or semantic equivalence. Key validation now has a separate
proved whole-closure nonempty-property check; its result does not establish the
other DL restrictions or key inference.

The structural arity stage now traverses the entire raw closure before any set
canonicalization. It checks minimum equivalence-class counts and original
pairwise disjoint/different members with the proved class/range/atomic relations,
includes recursive optional fillers and the key-property rule, and preserves
ordered property-chain repetitions. Exact success proves precisely this stage's
independent predicate, not all DL validation. Future normalization must retain
this validation order so semantic-changing duplicate removal cannot precede it.


Full axiom structural identity is now implemented by `axiom_equality`. The
complete comparator composes the class, range, atom and nested annotation
relations across every axiom constructor. The object and data key associations
are separate unordered sets. The two InverseObjectProperties fields remain
separate: Figure 14 names them objectPropertyExpression1/2, while its subproperty
chain association is explicitly ordered and nonunique. Thus reversed inverse
axioms can be logically equivalent while structurally distinct. This follows
Section 2.1 and the normative Figures 14/18, not merely the printed argument order.

General nested AST canonicalization can use the proved equivalence relation to
recognize copies, but still needs canonical-form and transformation proofs.
Structural semantic congruence and the actual outer axiom-set view are proved
below. Comparison itself retains every original object;
there is no silent deduplication or inferred logical equivalence. Arity checks
must precede canonical output, especially for disjoint/different associations.


### Structural semantic preservation and validation order

`StructuralCongruence` now connects the complete comparison relation to the
independent OWL Direct Semantics. Data-range identity preserves denotation for
arbitrary interpretations. Class identity including omission expansion requires
the normative interpretations of owl:Thing and rdfs:Literal; the full
IsInterpretation predicate supplies both. Object/data cardinalities count distinct
denotations on arbitrary domains, using the existing injection-based meanings.

Whole axiom satisfaction additionally requires distinct original structural
members for disjoint class/object/data, DisjointUnion and DifferentIndividuals
associations. This is supplied by the proved arity checker. It cannot be removed:
a checked counterexample compares raw DisjointClasses(Thing Nothing Thing) with
DisjointClasses(Thing Nothing). The first forces Thing empty under the occurrence
condition in Direct Semantics Table 5, while the second is satisfied by the
checked singleton interpretation. Structural set comparison alone accepts this
pair; the original arity stage rejects the repeated input. Two further checked
counterexamples show arbitrary non-OWL assignments cannot justify cardinality
omission expansion without the top interpretation conditions.

The theorem from actual Rust entry points requires successful complete axiom
comparison and successful arity checks for both original inputs. Closure-level
matching then preserves satisfaction and the same anonymous-assignment model
witness, full models, consistency and source/target entailment under a fixed
parameter datatype map and vocabulary. It permits infinite object/data domains
and assumes no distinct denotation for different names. Import standardization,
concrete datatype-map construction, canonical output, vocabulary assembly and
proofs of the actual future transformation remain separate release obligations.


### Validated outer axiom set and retained original occurrences

`axiom_set::build` is now an actual source-linked operation, not just a relation
between hypothetical outputs. Its input is the complete caller-supplied,
standardized-apart closure as `AxiomOccurrence { origin, axiom }` objects.
`origin` contains caller document/ordinal tokens. The builder first validates all
original arities and returns the exact first offending original object on failure.
Only after this complete scan does it group structurally equivalent full
annotated axioms. Origins do not define axiom identity, while annotations do.

The private `AxiomSet` borrows the original vector unchanged. It owns two index
vectors: all first representatives in increasing source order, and one minimal
representative index for every original occurrence. Public immutable accessors
expose original objects, both vectors and checked original/representative lookups.
Keeping all originals avoids losing import provenance when equivalent copies
share a class. No nested AST is rebuilt; a representative can still contain
permitted equivalent repetitions in unordered associations.

`AxiomSet.lean` specifies first representatives by structural minimality and
unique roots by a filtered mathematical index range. It proves actual builder
termination, exact arity acceptance, total public accessors, index bounds,
ordered unique structural classes, complete coverage and idempotent resolution.
The selected mathematical closure contains actual original axioms, inherits
arity acceptance and has the same structural classes. Composition with the
checked structural congruence yields models, consistency and entailment
preservation for a fixed normative parameter map and vocabulary on arbitrary
domains. These are preservation results; they do not execute OWL reasoning.

Parser-assigned source locations/scopes, canonical import assembly, duplicate-free
nested AST materialization and full DL validation remain release requirements.
As elsewhere, mathematical Vec/index bounds do not eliminate physical allocation
or stack exhaustion; typed operational limits remain the separate M8 scope.


### Functional Syntax names and prefix expansion

`rowl-frontend::names` recognizes complete PNAME_NS, PN_LOCAL, PNAME_LN and
BLANK_NODE_LABEL byte buffers. `Names.lean` gives independent codepoint languages
for the SPARQL 2008 productions referenced by OWL 2. Grammar construction and
strict UTF-8 recognition are composed to prove totality, exact acceptance and
malformed-unit diagnostics. Trailing dots, empty local parts, extra colons and
Turtle/SPARQL 1.1 local escapes cannot enter through these OWL grammars.

`prefixes::check` borrows immutable declaration records containing name and
namespace bytes. The private table constructor checks all records in source
order: name grammar, four reserved implicit names, absolute namespace IRI grammar,
then exact duplicate names among prior records. Even an unused declaration is
checked, and identical namespace bindings do not permit repeated names. Errors
retain original records; successful tables retain every original name/namespace
and satisfy `Prefixes.WellFormed`. Case and Unicode normalization are untouched.

`standard`, `namespace`, `declarations` and `lookup` have exact total contracts.
Namespace lookup returns owned bytes using proved copying operations supported
by the pinned extraction backend. `expand_parts` takes prefix/local byte parts,
checks their grammars itself, looks up the exact namespace and concatenates
without normalization. Incremental append checks avoid a native overflowing
sum; the proved contract uses mathematical lengths. The final absolute-IRI check
is necessary even when the namespace and local grammar separately pass: an IPv6
authority suffix and plane-ending Unicode characters are regression examples.
Each typed outcome has an independent phase-priority specification.

This is a complete lexical macro-expansion component. Source prefix declaration
punctuation, token boundaries and source locations are now handled by the proved
leading-prefix reader described below. Whole-document parsing, relative base
resolution for other serializations and canonical import scope assignment
remain separate M3 release obligations. Mathematical termination still uses the
pinned Rust execution model; physical allocation/stack limits remain M8 work.


### Greedy regular-language prefix matching

`longest::longest_prefix` takes an owned regular expression, immutable source
bytes and a byte position. The scan tests nullable recognition at each canonical
UTF-8 boundary, saves the newest accepted endpoint and advances the derivative.
The complete suffix is decoded even after the grammar stops accepting; malformed
UTF-8 therefore returns first-unit evidence rather than a successful partial
prefix. `Matched(None)` denotes no matching segment; `Matched(Some(start))`
denotes an accepted empty word. Nonempty lexer-token grammars must separately
exclude the latter to establish token progress.

`Longest.lean` defines exact canonical UTF-8 segments, language-membership
candidate endpoints and an independent mathematical maximum. It proves actual
termination, all-and-only exact matching outcomes and endpoint bounds. A retained
candidate invariant uses coverage by greater accepted endpoints, so replacing an
older accepted endpoint is justified mathematically. Grammar derivatives use
the already checked regular-language preservation theorem. Tests compare finite
languages with an independent string-prefix search at every UTF-8 boundary and
cover greedy keyword/name competition, multibyte repetition, empty inputs,
invalid positions and malformed suffixes after prior accepts.

This operation supplies greedy lexical matching required by OWL Functional
Syntax section 2.2. Complete terminal grammars and greatest-endpoint selection
are proved in the next component. Complete disjointness and stream rules are
also proved below; byte-to-ontology parsing remains pending.
Source text XML-character validation is a separate existing operation; this
primitive intentionally recognizes arbitrary supplied regular alphabets.


### Complete Functional Syntax terminals and selection

`functional` compiles all 84 terminal classes in the normative 2012 grammar:
71 case-sensitive keywords, four punctuation, seven variable terminals and
whitespace/comments. `Functional.lean` states independent codepoint languages
and proves exact compilation, complete byte recognition, longest-prefix
acceptance and nonempty bounded progress. Full IRIs use the existing absolute
RFC 3987 language; names use the OWL-referenced SPARQL 2008 grammar. Quoted
strings admit XML characters except unescaped quote/backslash, and exactly
`\"`/`\\` escapes. Multiline strings are valid; N-Triples escape forms
are not silently imported. `languageTag` uses the explicitly referenced RFC 5646
`langtag` subproduction, distinct from the broader RDF well-formed recognizer.

`next_terminal` compares the actual longest result for every inventory member.
The first-order fixed enumeration avoids caller eligibility metadata. The
independent `FunctionalSelection.Correct` predicate defines membership and a
greatest endpoint across the entire terminal type and the earliest eligible
inventory member at that endpoint. Complete token identity is uniquely determined,
and actual selection equals that independent predicate. Proved total correctness,
all-and-only token availability and source progress establish this token step.
Malformed UTF-8 in the complete suffix remains a typed first-unit error.

The audited inventory matches keyword spelling in compiler and independent
specification, visits in actual selection and specification, and the complete
model constructor inventory. This audit complements the checked language proofs;
it does not prove the English standard. Complete terminal-language disjointness
is proved below; full byte-to-ontology construction remains pending. Canonical
selection at tied endpoints, quoted payloads and whole-source token streams
are proved separately.
The public example prints real source slices and illustrates keyword/name
competition without asserting a parsed ontology or reasoner result.


### Functional Syntax quoted-string payloads

`functional_payload::read_quoted` composes the already verified strict unit
reader, expected opening quote, XML-character checking, a quote/backslash-only
escape reader, canonical scalar encoding, bounded output append and a progressing
body loop. It returns owned decoded bytes plus the first byte after the closing
quote. The output budget counts decoded bytes, excluding source punctuation and
escape backslashes. First diagnostics retain original source positions; a
failed partial append cannot expose a successful payload.

`FunctionalPayload.lean` independently specifies decoded raw/escaped units,
delimited bodies, exact canonical encoded-unit concatenation and every first
failure phase. Actual total correctness and acceptance iff the payload grammar
and budget hold are checked. No non-scalar value reaches the encoder failure
branch. Both directions of source-language equivalence connect these byte
relations to `Functional.TerminalLanguage QuotedString`. Every matching source
segment has a decoded payload; a fitting caller budget guarantees the actual
reader returns that exact payload and ending offset.

The reader validates the token prefix through its closing quote. It intentionally
stops before any following tag/datatype/other text; the separate terminal
selector validates the whole suffix. Whole-source separators/trivia are now
composed below; other payload kinds, ontology construction and import scope/provenance assembly
remain separate M3 obligations. Physical resources and cancellation remain M8.


### Whole-source Functional Syntax token streams

`functional_lexer::lex` first validates the complete UTF-8/XML source, then emits
immutable source spans using the proved 84-terminal selector. Whitespace and
comments are discarded, including leading/trailing trivia. Regular-token
boundaries compose all seven normative delimiters, exact final Unicode
codepoints, EOF and greatest whitespace/comment endpoints. The caller's token
limit counts emitted regular tokens, with trivia costing zero. A later failure
returns its first original diagnostic without a successful partial stream;
initial malformed/non-XML text takes precedence over token-limit failures.

`FunctionalLexer.lean` defines source-language endings and separator relations,
independent whole-stream derivations and exact ordered, nonempty, bounded
regular-token spans. Totality and both directions of whole-source acceptance
are composed from the actual extracted loop. All recursive calls strictly
advance in the source; native subtraction is proved safe. InvalidSpan is proved
unreachable from the public byte entry point. No caller supplies trusted token
kinds, boundary metadata or UTF-8 assumptions to that public theorem.

The normative section 2.2 step-6 prose does not explicitly exempt a matched
special terminal. Applying it literally after a standalone whitespace token
would reject leading whitespace before keywords and whitespace after the
`^^` token, despite the standard's examples accepting spaced literals.
This lexer applies separator enforcement after regular tokens and restarts
matching after discarded special tokens. This documented specification
interpretation is reflected in the independent derivation relation; Lean does
not mechanically establish the intended meaning of English prose. EOF needs
no separator. Deterministic inventory priority is proved exactly, while the
standard's separate assertion of pairwise terminal-language disjointness
is now proved below. Full Functional Syntax document parsing and
byte-to-ontology/import assembly are still pending; lexically valid sequences
can contain unmatched parentheses or wrong axiom arities. Physical machine
resources, cancellation and a release-safe API remain M8 work.


### Complete terminal disjointness and priority-free greatest matching

`Functional.keyword_words_injective` proves that all 71 independent standard
keyword spellings are distinct. `FunctionalDisjointness.lean` proves that the
complete terminal languages are pairwise disjoint on arbitrary Unicode words.
Its private mathematical discriminator distinguishes fixed initial markers,
digits, whitespace and name/keyword forms; the latter use colon occurrence and
the last codepoint. Required properties are derived from the exact independent
languages, including all SPARQL 2008 base-character intervals, nonempty local
names and their exclusion of colon. This discriminator is a proof device;
the actual Rust selector does not execute it.

Canonical UTF-8 spans with equal source endpoints have identical words, so
`candidate_kind_unique` lifts word-language disjointness to the actual original
byte candidates. The standard `Greatest` predicate specifies only valid UTF-8,
the original start, terminal membership and endpoint maximality. No inventory
priority is supplied. `greatest_correct_iff` derives the former first-candidate
condition, `greatest_token_unique` proves exact token identity and
`next_terminal_greatest_iff` establishes both directions of actual acceptance.
Thus the implementation's deterministic fallback cannot affect any matched
token; the normative section 2.2 no-ties assertion is now proved for the stated
complete grammars. The separately documented step-6 prose interpretation,
full document syntax/AST construction and byte-to-OWL integration remain open.

### Exact cardinality integer payloads

The kernel's `decimal::read_span` consumes unchanged original source bytes and
constructs the existing `probes::Natural`, also used by all six raw OWL
cardinality-expression forms and their independent semantics. It checks span
bounds and nonemptiness before indexing, accepts only ASCII decimal digits,
computes each positional step through proved exact addition, and reports the
first invalid digit at its original byte offset. `decimal::read` supplies the
complete-byte entry point. Neither operation trims, accepts a sign or normalizes
Unicode digits. Leading zeroes retain their correct mathematical value.

`Decimal.lean` establishes total correctness, exact value, both directions of
acceptance and range/empty/first-digit diagnostics. `FunctionalIntegers.lean`
proves that canonical ASCII source spans are their exact original byte values,
then equates independent Functional Syntax integer candidates with bounded
nonempty digit spans. The actual reader accepts precisely those grammar words
and gives their positional value. Actual greatest-selected integer tokens and
every integer in an accepted whole-source stream supply this exact value at
their original endpoints. The proof composes the independently extracted
frontend and kernel over the same immutable bytes; no cross-crate external
implementation or caller span metadata is assumed correct.

This completes the integer payload stage. Parsing the surrounding cardinality
expression, remaining IRI/name payload construction, complete document syntax,
byte-derived imports/scopes and full OWL validation/reasoning remain pending.
The unary natural representation has no mathematical machine-integer cap, but
its cost is proportional to its represented value. Physical memory/stack,
efficient arithmetic and typed cancellation/resource outcomes remain M8 work.

### Canonical source spans and nonquoted name values

`SourceSpans.lean` proves complete canonical UTF-8 source/copy equivalence for
arbitrary Unicode words, exact rebasing of complete units, the minimum byte
width of a source word and splitting concatenated words at original canonical
byte boundaries. These are mathematical source laws used by the actual copied
byte readers; malformed bytes outside a selected segment remain a separate
whole-source lexer obligation.

`functional_names::read_span` checks bounds before arithmetic/indexing, copies
and revalidates the full standard terminal, then copies the exact value with
only the fixed syntax markers removed. Full IRIs strip `<`/`>`, node IDs strip
`_:`, and language tags strip `@`. Prefix and abbreviated names retain their
complete spelling, including colon. The returned byte budget excludes stripped
markers. Case, percent sequences and Unicode spelling are preserved exactly.
Range errors identify the original token start; invalid-token errors identify
the entire source span start, not an asserted first offending character. Budget
errors identify the original payload start. No partial value is returned.

The `FunctionalNames` proofs establish total correctness, complete successful
value/acceptance and complete phase/offset rejection in both directions. They
also prove the value grammars after marker removal, including absolute IRIs,
SPARQL 2008 blank/name forms and the normative RFC 5646 langtag subproduction.
Actual greatest-selected names and all five families throughout successful
complete lexer streams have their exact values when each payload fits.

This completes verbatim nonquoted value reading. Source-derived splitting and
IRI resolution now compose it with the immutable prefix table, as described below.
Leading prefix grammar is proved below. Remaining header/body grammar, role assignment, canonical anonymous scopes, complete
literal/document AST construction, import provenance and full M3/M4 composition
retain their original release gates. Physical resources/cancellation remain M8.
Distinct Rust error/type names avoid a derived-instance namespace collision in
the pinned extraction tool; generated code is not rewritten to assume it away.

### Source-derived Functional Syntax IRI resolution

`functional_iris::split_abbreviated` revalidates the complete original source
span, then scans actual canonical UTF-8 scalars to derive the first syntax colon.
The original prefix includes its colon; the local field retains exact bytes.
The independent `Partition` specification describes both grammatical source
segments and exact copied fields. The proof derives the absence of a colon in
all permitted prefix-body codepoints from the complete SPARQL 2008 grammar;
no supplied separator, string normalization or extraction assumption is used.
Independent partitions are unique. Splitting has totality, exact value/acceptance
and all diagnostic equivalences in both directions, and its internal copy/colon
fallbacks are proved unreachable after valid source acceptance.

`functional_iris::resolve_span` composes full-IRI reading or source-derived parts
with the already proved checked immutable prefix table. Abbreviated IRIs use
exact case-sensitive lookup, all four implicit standard namespace spellings,
verbatim namespace/local concatenation, final-output byte limits and complete
RFC 3987 absolute-IRI revalidation. Total correctness, exact successful results,
complete admissibility, all rejection phases/offsets in both directions and final
IRI grammar are proved. Source spelling may be longer than the expanded IRI;
only the final returned bytes consume the caller output limit. Full-IRI budget
errors retain the original payload start, while abbreviation expansion errors
retain the whole original token start. Invalid token errors identify the supplied
span, without asserting a finer first-invalid-character diagnostic.

The resolver receives a table through its checked constructor. The source prefix
reader and composition below now derive its exact declaration records from bytes.
Remaining ontology header/body grammar, semantic role assignment,
canonical anonymous scopes, complete literal/document AST construction and
byte-derived import metadata/provenance remain pending. The resolver validates
its own spans; acceptance of bytes outside them remains the whole-lexer duty.
Physical allocation/stack and typed cancellation are separate M8 obligations.

The source resolver retains explicit Result branches for the restricted extracted
control flow. Its targeted question_mark style-lint exception adds no semantic
assumption; the actual branches remain covered by the complete source proofs.

### Source prefix declarations and the ontology opening

`functional_prefixes::read_prefix_header` takes the complete original byte buffer
and separate emitted-token, declaration-count and per-value byte limits. It first
runs the proved whole-source lexer: a malformed later suffix rejects the source
before any prefix-stage syntax or payload checks. It then reads the maximal
leading sequence `Prefix ( prefixName = fullIRI )` and the exact `Ontology (`
opening. The source tokens for that opening and the entire remaining token
stream are returned unchanged. Optional ontology/version IRIs and leading
imports are proved in the following component. Annotations, axioms and final
closing punctuation belong to the future full document parser. In particular,
accepting `Ontology(` here is intentional and
does not establish that an ontology document is complete or valid.

`FunctionalPrefixShape` gives an independent five-token declaration grammar and
first-mismatch relation. The actual shape reader is total and every exact shape
or syntax failure is equivalent to this relation. `FunctionalPrefixDeclaration`
composes the source name readers, proving exact prefix/namespace payloads,
per-field budgets, complete values/errors and unchanged suffixes. All five
syntax tokens are checked before the prefix payload, then the namespace payload.
Each accepted body consumes exactly five tokens; including its Prefix keyword,
repeated scanning decreases the token count by six. The `FunctionalPrefixes`
run/section specifications prove ordered maximal scanning, exact rows/opening,
declaration-count limits, all syntax/value/count diagnostic phases, public
byte-to-result totality and complete successful acceptance. EOF errors use the
original whole-source byte length; mismatches use the actual first token start.
Declaration-count limits are checked at the Prefix keyword before its body.
Lexical errors retain the existing lexer evidence; InvalidSpan is unreachable.

The reader retains duplicate and reserved declarations, even when unused. Callers
must run `prefixes::check` before using them: syntactically valid rows alone do
not establish the normative namespace-table rules. The checked-source theorem
proves that the successful immutable table retains precisely the parsed row
vector. `FunctionalPrefixResolution` composes the actual byte reader, table check
and source IRI resolver. Its exact value/error equivalences use those original
source-derived namespace records; no caller-supplied namespace metadata or
spelling normalization is introduced. This closes that parser-to-resolution
boundary, while complete OWL AST/import construction and M3/M4 release remain
pending. Explicit Result branches and their targeted style-lint exception keep
control flow compatible with the restricted extraction. Physical stack/allocation
and cancellation remain separate M8 obligations.

### Source ontology identity and import references

`functional_header::read_header_tail` consumes the unchanged stream after
`Ontology (` and borrows its already checked prefix table and original byte
buffer. It reads the standard `[ontologyIRI [versionIRI]]` alternatives followed
by the maximal leading `Import ( IRI )` sequence. Both full and abbreviated IRIs
use the proved source-span resolver. Returned HeaderIri records retain the exact
original token and resolved byte value; SourceOntologyIdentity permits a version
only with an ontology IRI. Import records retain the original keyword, target
token/value, order and repetitions. Final IRI limits count returned bytes, so a
long source prefix can expand under a shorter limit. No normalization occurs.

The independent OptionalRun/IdentityRun relations distinguish absent, one and
two values and exact first IRI failures. Absent reading preserves the complete
original suffix; present reading consumes exactly its own token. The shape/body
relations for imports establish all three original syntax tokens before target
resolution. First EOF mismatches use the original complete byte length, including
discarded trivia; wrong token errors retain their start. Each Import keyword
checks the reference-count limit before its body. Accepted bodies consume three
tokens and the repeated scanner consumes four including the keyword, establishing
termination without a fuel cutoff. ScanRun/TailRun/ImportSection establish exact
ordered records, all first error phases in both directions, bounded count,
maximal stopping and an unchanged empty or first non-Import suffix. No partial
reference vector is returned on a later import error.

FunctionalHeaderSource composes actual complete byte prefix lexing/parsing,
normative table checking and header-tail reading. Exact successful values and
every header error use precisely the original parsed namespace records; the
header value theorem connects original identity/import tokens, source grammars,
budgets and untouched suffixes. The low-level header reader does not independently
lex the complete source; callers use the preceding byte stage as in the example.
Unexpected trailing IRIs/tokens, ontology annotations, axioms and final closing
syntax remain for the full document parser, so a missing closing body can still
succeed at this partial stage. Import IRI references are now source-derived, but
canonical IRI catalog/index assembly, full document validity, anonymous scopes,
provenance and complete M3/M4 integration remain pending. Physical stack/heap
limits and cancellation remain M8 work.

The SourceOntologyIdentity name differs from the kernel's raw OntologyIdentity
to avoid unqualified derived-instance collisions in the pinned extractor.
The generated translation is regenerated from Rust, with no manual rewrite or
new assumption. Explicit Result branches retain the existing targeted style-lint
exception for restricted extracted control flow.


### Functional Syntax literals and required plain-string expansion

The source literal reader follows the [2012 literal grammar and expansion rules](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Literals).
It consumes exactly one quoted-string token, optionally followed by a language
terminal or by ^^ and one full/abbreviated datatype IRI. All shape syntax is
checked before decoding; every payload span is revalidated on original bytes.
Returned fields retain original quote/form tokens, exact source language case,
exact decoded lexical bytes for explicit types and the untouched suffix.

Untagged/tagged strings obligatorily expand to rdf:PlainLiteral with lexical
payload + '@' + exact language bytes, empty for an untagged string. Internal '@'
is preserved, so untagged mail@example.org becomes mail@example.org@. Explicit
rdf:PlainLiteral lexical bytes are not modified. Normative datatype lexical/value
admissibility is separate M5 work; this component may read raw ill-typed values.
It is separate from the RDF 1.1 literal representation and input conventions.

Independent shape, span, finishing and complete Run relations prove totality,
all exact results/errors in both directions, preserved source values/suffixes,
mandatory expansion, both final output budgets and strict one/two/three-token
progress. Syntax precedes quote decoding, range checks precede decoder failures,
quote decoding precedes tag/IRI reading, and plain lexical expansion precedes the
constant datatype budget. Whole-byte prefix parsing and normative table checking
compose on precisely those original namespace rows; the caller still supplies
the literal position. Full annotation/axiom/document assembly and canonical
imports/scopes remain pending. Physical memory/stack/cancellation outcomes remain
outside the mathematical execution model until M8.
