# M2 specification and reviewed correspondence

Sources: [2012 Direct Semantics](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/)
and [2012 Structural Specification](https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/).
The independent specification is `verification/Rowl/OwlSemantics.lean`; its input
types are generated from `crates/rowl-kernel/src/model.rs` by pinned Charon/Aeneas.
There is no independent substitute AST and no assumed reasoning algorithm.

Raw IRI spellings are now exact `Vec<u8>` buffers. The formal built-in constants
use their literal UTF-8 byte spellings. This allows the actual AST collector,
interner and declaration validator to share one representation without an
unsupported Rust `String` equality/conversion model. UTF-8 and absolute-IRI
validity are frontend obligations; arbitrary raw byte values do not become
valid IRIs merely because a semantic predicate can be evaluated over the AST.
Literal lexical forms and anonymous scope/label fields also use exact raw byte
vectors. Actual structural comparisons are checked without a string-conversion
assumption. Parameter datatype maps operate on byte spellings with an explicit
`Utf8Lexical` representation condition: admitted lexical forms are sequences of
canonical RFC 3629 units. `literal_lexical_utf8` proves the consequence for a
valid vocabulary literal. This condition includes decoded U+0000 and differs
from XML source-character admissibility. The actual normative datatype map,
lexical-space checks and canonical import scoping remain later obligations.
Malformed raw bytes remain constructible; comparison is not validation.

| Standard part | Formal definition | Representation/interpretation decision |
| --- | --- | --- |
| §2.1 datatype map | `DatatypeMap`, `ValueEmbedding`, `IsVocabulary` | Six components and range conditions; embeddings preserve actual datatype values and permit extra data-domain elements |
| §2.2 interpretations | `Interpretation`, `IsInterpretation` | Nonempty separate object/data sorts; tagged sum makes them disjoint; independent entity-role maps implement punning; built-ins and literal/facet agreement are explicit conditions |
| Table 1 | `objectRelation` | Inverse exchanges endpoints; actual Rust inversion is checked in `OwlLaws` |
| Table 3 | `dataDenote` | Six exhaustive cases; complements use the whole data domain; enumeration uses literal values; restrictions intersect datatype and facets |
| Table 4 | `classDenote` | 18 exhaustive cases; absent qualifiers mean unrestricted fillers; standard unary datatypes give one property per data quantifier |
| Tables 5–8 | `satisfies` | Class/property axioms, ordered chains, all property characteristics and datatype definitions |
| Table 9 | `satisfies` / `HasKey` | Subjects and shared object fillers require NAMED; data fillers have no NAMED requirement; either key list may be empty |
| Table 10 | `satisfies` | Equality, pairwise inequality, class/property assertions and negative property variants |
| §2.3.7 | `AxiomClosure`, `satisfiesClosure` | All closure axioms; imports and standardization apart must already have been computed |
| §2.4 | `modelsClosure`, `Model`, `withAnonymous` | Existential reassignment of anonymous input individuals with every other component fixed |
| §2.5 | `Consistent`, `Entails`, `Equivalent`, `Equisatisfiable`, `ClassSatisfiable`, `Subsumed`, `InstanceOf`, `Answers` | Universe-polymorphic definitions over all models; query implementation/reductions and simple-property validation remain later obligations |
| Introduction / annotations | `satisfies`, `satisfiesAnnotated` | Declarations and annotation axioms have no logical constraint; nested metadata is retained |

The constructor-to-meaning inventory is `docs/model-inventory.json`.
`scripts/verify.py` checks its Rust variants and each exhaustive Lean match.
Lean checks structural termination, including children inside vectors and optional
qualifiers. Public theorem and selected semantic-definition assumptions are
audited against `verification/theorems.json`.

## Cardinality and identity

`AtLeast n P` requires an injective map from `Fin n` to distinct denotations
satisfying P. `AtMost n P` excludes such a map of size n+1. `Exactly` combines
the two. This covers infinite domains without interpreting an infinite set's
finite `ncard` as zero. Checked laws establish at-most-one/functionality,
singleton exact cardinality and infinite-set behavior. Different names or
literals may have equal denotations; no unique-name assumption is imposed.

Unordered structural associations are raw sequences in M2. Minimum written
arities are enforced by types; duplicate removal, unordered structural equivalence
and validation belong to M3–M4. Property chains retain order and repetitions.
Disjointness and difference use pairwise positions, preserving the distinction
between structural names and denotations. Semantics is intended for canonical,
well-scoped OWL structures. A predicate on an invalid raw AST does not validate it.

NAMED contains denotations of named individuals in the vocabulary; it need not
contain every possible IRI, nor be exactly the set of named denotations.
Anonymous individuals can coincide with named individuals. Scope tokens preserve
structural blank-node identity but do not assert logical inequality.

## Checked examples and limits

`OwlLaws.lean` proves functionality-induced equality and explicit-difference
conflict, universal vacuity, unnamed existential witnesses, chain composition,
key NAMED restrictions, annotation/declaration irrelevance, anonymous reassignment
invariance and entailment by inconsistency. `OwlExamples.lean` provides checked
interpretations with an empty class, coincident names, anonymous reinterpretation
and an unnamed witness. These examples use an explicitly empty parameter datatype
map, not the normative OWL datatype implementation. Unused map-carrier elements
do not impose extra data-domain cardinality constraints.

These are proofs relative to the independent formal definitions, not correctness
proofs of a full OWL decision algorithm. No byte parser, imports computation, DL
validation, normative lexical/numeric datatype map, tableau or automatic
classification is implemented. Correspondence to W3C prose/tables is a reviewed
specification choice; a mechanical proof of the English document is not claimed.
