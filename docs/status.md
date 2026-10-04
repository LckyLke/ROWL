# Implementation status

M0, M1 feasibility probes and M2 structural representation/independent semantics
are complete. M3 and M4 have verified components; both milestones remain in
progress. Full OWL parsing and executable reasoning are still future work.

## Working now

- Four Rust workspace crates; unsafe forbidden, publication disabled.
- The original two-atom Boolean kernel, with checked soundness, completeness and
  termination linked to the actual Rust extraction.
- Four further M1 operations with total-correctness proofs: Vec slot mutation,
  ASCII digit recognition, recursive immutable opaque-key/byte lookup, and exact
  unary-natural addition. These are primitives, not a parser or import closure.
- M2 raw role-typed structures: all 18 standard class forms, six data ranges,
  37 axiom variants, entities, scoped anonymous individuals, literals, nested
  annotations, ontology/version headers and import references.
- Actual Rust property inversion, proved total, involutive and semantically correct.
- Independent Lean Direct Semantics over extracted Rust types: interpretation,
  datatype-map/vocabulary conditions, expression and axiom meanings, closure
  satisfaction, anonymous reinterpretation for models and inference definitions.
  Domains can be infinite; data domains may extend the datatype map.
- M3 symbol-indexed catalog closure with termination on cyclic imports, exact
  reachability, verbatim payload preservation and duplicate/missing-document
  diagnostics. Import metadata is supplied explicitly; OWL byte parsing is pending.
- M3 strict RFC 3629 UTF-8 decoding with exact byte offsets and XML character
  checking. Complete text acceptance is proved in both directions; malformed
  units and forbidden characters return the first unit offset.
- M3 composition of indexed closure and reachable-source text checks, retaining
  verbatim bytes and diagnosing the failing document. This is a UTF-8 text stage,
  not a grammar parser or support for every XML encoding.
- M3 raw RDF 1.1 positional terms and datasets, with a default graph and explicit
  named-graph records, including empty graphs and shared scoped blank identities.
  Actual graph selection checks unique names, distinguishes missing from empty,
  and retains the whole dataset. Exact name comparison, total correctness,
  selection preservation and both acceptance equivalences are proved.
  Term lexical validity, parser-assigned scopes and serialization remain pending.
- M3 whole-byte regular-language recognition: exact structural copying,
  nullable/union/concatenation/Kleene closure laws, derivative preservation,
  total UTF-8 scanning, sound/complete acceptance and exact malformed-unit
  diagnostics. Grammar mismatch does not hide a malformed suffix.
- M3 complete RFC 3987 IRI and IRI-reference lexical recognition from bytes,
  including IPv6/IPvFuture, all Unicode ranges, percent escapes and query-only
  private characters. The actual compiled grammar is proved equivalent to the
  independent ABNF language; bounded repetition is proved exact. IRI includes
  fragments. Base resolution and ontology integration remain pending; Functional Syntax
  prefix expansion is separately proved below.
- M3 canonical fixed-size UTF-8 encoding: total for every u32, None exactly
  for non-scalars, unique canonical RFC byte grammar, complete encoded-unit
  acceptance, inverse and composition with
  the actual strict decoder, including the exact consumed byte offset.
- M3 full RFC 5646 well-formed language-tag recognition from bytes: compiled
  grammar equivalence, total Boolean checking and sound/complete acceptance.
  Grandfathered/private/extension tags and ASCII case-insensitive tokens are
  included. Registry validity and its duplicate restrictions are separate.
- M3 actual N-Triples unit, required-character and expected-character readers;
  maximal comments and both whitespace modes, with exact offsets, first-error
  diagnostics and acceptance in both directions. UTF-8 unit append budgets,
  all token character ranges, hex digit values and exact bounded span copying
  are proved. The complete blank-node token reader composes these stages,
  preserving the caller scope and exact label bytes and recognizing the
  maximal label with trailing-dot backtracking. This proof starts at the token's
  source bytes; it does not yet establish a whole-document graph parser.
- M3 complete Unicode/short escape payload decoding: exact four/eight hex
  digits, natural numeric values, all eight ECHAR forms, scalar validation and
  IRI/string mode restrictions. Totality, complete acceptance, exact first-stage
  errors and bounded advancing source offsets are proved.
- M3 complete quoted IRI/string tokens: actual backslashes, raw character
  restrictions, opening/closing delimiters, canonical UTF-8 output and byte
  budgets are composed. Total correctness, acceptance iff the independent
  grammar/budget hold, exact first diagnostics and source progress are proved.
  IRIREF additionally composes the RFC 3987 absolute-IRI recognizer, preserving
  exact decoded spelling. Subject construction composes those IRIREF and
  caller-scoped blank tokens with total correctness and complete acceptance.
- M3 complete LANGTAG byte tokens: maximal ASCII head/subtag and nonempty
  hyphen-suffix scanning, exact source spelling/case, bounded copying and the
  RFC 5646 ABNF recognizer are composed. Totality, complete acceptance,
  bounded progress and exact first-stage diagnostics are proved.
- M3 complete N-Triples byte-to-graph reading: literal kind binding, subject/object
  construction, triple punctuation/line boundaries and the public document loop
  have totality and complete-acceptance proofs. Exact ordered occurrences,
  repeated triples, caller-scope blank identities, term/count limits and first
  original-offset errors are preserved. Every triple strictly advances; no
  malformed suffix can expose a successful partial graph. Export laws remain pending.
- N-Triples read and experimental export with strict UTF-8, absolute IRIs, escaped
  lexical forms, well-formed tags, exact datatype spelling, scoped blank keys,
  comment/line handling and count/byte budgets. Serialization-isomorphism
  proofs remain pending. All 68 official W3C syntax
  cases pass, and positive cases round-trip through the writer with an
  independent blank-bijection/term-preservation check. See formats.md.
- M3 exact byte-key symbol table: duplicates reuse their first symbol, new keys
  receive stable consecutive symbols and count-capacity errors preserve the table.
  Forward/reverse lookup, unique-key invariants and old-symbol preservation are
  proved. Raw IRI spellings use the same exact byte-buffer representation, so
  collection and interning no longer require a Rust-string conversion assumption.
  The raw AST does not automatically invoke the new IRI byte validator.
- M4 declaration typing over supplied complete occurrence tables, including
  allowed punning, required property/class/datatype declarations and optional
  named-individual declarations. The composed raw-ontology operation now derives
  the occurrence tables itself and includes implicit built-in roles.
- M4 explicit entity collection over the full raw OWL AST: all 18 class forms,
  six data ranges, 37 axiom forms and nested annotations. Exact IRI spellings,
  roles, order and duplicates are proved; declarations are collected separately.
  Untyped annotation/header/facet IRIs and anonymous identifiers are excluded.
- M4 integrated declaration checker: complete raw AST collection, exact IRI
  interning, all 49 normative built-in declaration roles and the typing check.
  Lean proves total correctness and acceptance iff declaration constraints hold
  on the original IRI spellings, for every completed indexing run. No numeric
  symbol metadata is supplied by callers. Import assembly, lexical and global
  DL validity remain separate; this is not a full DL-validity result.
- M4 reserved-vocabulary checking from the actual raw ontology: all four reserved
  namespaces, exact built-in roles, ontology/version headers and nested ontology
  annotations. It catches reserved-role misuse that allowed punning does not.
  Total correctness, exact first-entity diagnostics and acceptance iff these
  restrictions hold are proved; it is separate from declaration checking.
- M4 complete anonymous positional checking on all class/axiom forms, including
  recursively nested enclosing annotations on the four prohibited axiom types.
  The closure scan is proved total, accepts iff the independent full positional
  predicate holds and returns the exact original first offending annotated axiom.
  Other axiom types may retain anonymous annotation values.
- M4 anonymous assertion-graph forest checking from the actual supplied complete
  raw closure. Scoped identities compare exact scope/label byte fields. Ordered
  graph projection and undirected connectivity are proved total; forest acceptance
  is exactly no self edges and no cyclic walks, with checked tree components.
  Duplicate endpoint pairs denote one graph edge.
  The named-boundary condition is proved separately below; canonical scopes from parsing/imports remain pending.
- M4 anonymous edge-multiplicity checking on the actual raw axiom occurrence
  vector, with totality and exact acceptance proofs. Equivalent annotated copies
  count once; distinct properties, inverse forms, orientations and annotations
  count separately. Failures retain both original annotated axioms.
- M4 total structural comparisons for literals, values, individuals, properties,
  recursively nested annotations and positive object assertions. Annotation
  associations use proved set equivalence, retaining nesting and atomic fields.
  Raw literal lexical forms are exact byte buffers; valid parameter-map literals
  satisfy a checked Unicode UTF-8 representation condition. General AST
  canonicalization, executable lexical validation and normative datatypes remain
  separate obligations.
- M4 named-boundary checking over the supplied raw closure: every anonymous
  graph component has a vertex incident to at most one structurally distinct
  positive assertion with a named endpoint. Endpoint projections, exact incidence,
  structural counting, complete component search and original failing
  endpoint evidence have totality and acceptance proofs. Other anonymous
  occurrences are isolated and qualify automatically.
- M4 `check_anonymous` composes all anonymous-individual restrictions: positional
  checking, forest validity, edge multiplicity and named boundaries. Its totality
  and exact acceptance are proved, including original diagnostic evidence and
  positions/forest/multiplicity/boundary priority. Run it before semantic assertion
  normalization. It still requires the supplied complete standardized-apart
  closure; byte-derived imports/scopes and other DL restrictions remain pending.
- M4 total exact structural comparison of all six data-range constructors,
  recursively unordered range/literal/facet associations and annotated datatype
  definitions. Range equivalence is proved reflexive, symmetric and transitive;
  definition equivalence has the same laws on definition axioms. Constructors,
  nesting, exact IRI/lexical bytes and recursive annotations remain significant.
  Distinct minimum arities are checked below; full AST canonicalization and
  datatype value/facet validation remain separate.
- M4 datatype-definition availability and uniqueness over the actual supplied
  complete axiom closure, deriving every explicit occurrence from the full raw
  AST collector. Custom datatypes require one structurally distinct annotated
  definition; predefined names permit no redefinition. The actual operation is
  proved total with exact acceptance and original missing/conflicting evidence.
  Dependency acyclicity and defined-datatype positions are proved separately and
  composed below. Normative lexical/facet/value spaces and complete DL validation
  remain pending.
- M4 complete datatype-definition dependency-order checking from actual raw
  range occurrences, including literal datatypes and excluding enclosing metadata.
  Exact directed reachability is proved total on cyclic/repeated inputs and
  restores the owned graph. Graph acceptance is equivalent to the normative
  strict partial order on the actual datatype carrier. Rejections retain an
  original dependency with a reverse path and prove no permitted order exists.
- M4 `check_definition_rules` composes availability/uniqueness and the full
  dependency-order restriction, with totality, exact acceptance, original failure
  evidence and availability-before-cycle diagnostic priority proved. Cycles are
  distinct from missing or multiple definitions. Positional restrictions are
  proved separately below; normative lexical/facet/value validation and other
  DL restrictions remain pending.
- M4 complete defined-datatype positional validation from actual closure
  definitions: every range/class/axiom form, optional fillers and recursive
  annotations. Named ranges may use defined datatypes; literal datatypes and
  restriction bases may not. Totality, exact first original failures and exact
  acceptance are proved. Supplied ontology annotations are also checked before
  axiom positions; imported annotations require the same complete definition closure.
- M4 `check_structural_datatypes` composes definition availability/uniqueness,
  dependency order and all supplied positional restrictions. Totality, exact
  conjunction acceptance, original diagnostics and definition/order/ontology-
  annotation/axiom-position priority are proved. Concrete lexical/facet/value
  validation, import assembly and remaining DL constraints stay separate.
- M4 top-data-property occurrence checking: the only allowed typed occurrence
  is the superproperty of SubDataPropertyOf. The full raw AST traversal catches
  nested restrictions, key members, declarations and data assertions. The
  supplied complete axiom scan is proved total, returns the original first
  violating annotated axiom and accepts iff its independent restriction holds.
  Annotation IRI references retain their separate role.
- M4 complete raw role-fact preprocessing: all typed object-property names and
  both orientations, inverse-closed hierarchy edges, composite seeds, every
  nested cardinality/self requirement and the restricted property-axiom uses,
  plus original ordered chain references. Full axiom/closure traversal and
  exact AllOPE membership, hierarchy-edge membership and composite-root membership are proved. Independent simplicity and regularity predicates are defined. Simplicity and non-simple closure propagation are proved separately below;
  the property-chain regularity decision is proved separately below.
- M4 actual cyclic/duplicate-tolerant composite reachability and the complete
  raw-axiom simple-role checker. Totality and exact non-simple membership are
  proved; the raw collector supplies every reached node. The checker accepts
  iff the independent simple-role restriction holds, preserves the first
  forbidden required role and has no reachable missing-node outcome. This is
  one DL restriction; the separate regularity decision is described next.
- M4 full property-hierarchy regularity decision over the supplied raw closure.
  The actual chain compiler preserves the five normative alternatives, the
  finite pair worklist computes the least transitive/inverse-source relation,
  and reverse-hierarchy checks decide existence of a permitted strict order.
  Totality, success iff the independent regularity predicate, a concrete order
  on success and unavoidable conflict evidence on rejection are proved. Both
  missing-universe outcomes are excluded for raw syntax. This certifies this
  restriction; full DL validation and byte-derived import closure remain pending.
- M4 exact semantic preprocessing: inverse positive/negative assertion
  canonicalization, universal subclass constraints and annotation preservation,
  with anonymous-assignment model equivalence. Ordered batch preparation now
  preserves every occurrence, its caller-supplied origin tags and annotations,
  with model equivalence for the entire batch.
- M4 complete class-expression structural comparison: all 18 forms, recursively
  unordered members, exact unbounded cardinalities and normative defaults for
  omitted qualifiers. The actual Rust comparison is proved total and exact;
  the independent relation is proved reflexive, symmetric and transitive.
  This retains nesting and constructor kinds; logical simplification, canonical
  output remain separate; distinct-minimum-arity checking is proved below.
- M4 nonempty key-property checking from supplied raw axioms: a HasKey must have
  an object or data key member. Totality, exact acceptance and the first original
  annotated failing axiom are proved. This does not yet implement key inference.
- M4 full structural arity checking over the actual supplied raw closure: all
  class/data/axiom forms, nested fillers, recursive equivalence-class minimum
  counts and the nonempty-key rule. Pairwise duplicate-disjointness validation
  implements the explicitly documented compatibility decision before dropping
  occurrences; ordinary repeated members require two distinct classes and
  ordered chains retain repetitions. Totality, exact acceptance and the first
  original annotated failure are proved. This does not supply canonical output,
  the RDF self-disjointness conversion, lexical/value validity or full DL validation.
- M4 full annotated-axiom structural comparison over all 37 forms. Body and
  complete annotated relations are total, exact, reflexive, symmetric and
  transitive. Unordered associations and nested metadata ignore equivalent
  repetitions; chains and separate inverse-property fields retain their order.
  Keys have separate object/data sets; atomic identity and qualifier defaults
  remain exact. Compatibility with the existing assertion/definition checkers is
  proved. Canonical output and model-preserving whole-AST canonicalization remain pending.
- M4 full structural semantic congruence against the independent OWL Direct
  Semantics: all data, class and axiom forms, including cardinality defaults.
  Those defaults require normative interpretation conditions; disjoint/different
  associations require original occurrence-distinctness, supplied by actual
  arity checks. Actual comparison plus arity acceptance certifies satisfaction
  equivalence. Structurally matching arity-valid supplied closures preserve
  anonymous-assignment models, full models, consistency and entailment for each
  fixed datatype map and vocabulary on finite or infinite domains. Checked
  counterexamples establish why these premises cannot be omitted. This is a
  preservation theorem, not an implemented whole-AST canonicalizer or reasoner.
- M4 actual validated outer axiom-set construction. All original arities are
  checked before grouping complete annotated structural classes. Stable first
  representatives, every original document/ordinal record and an exact
  per-occurrence mapping remain accessible through immutable borrowed views.
  Constructor/accessor totality, minimum representatives, ordered unique classes,
  coverage and idempotence are proved. The selected closure preserves full
  models, consistency and entailment under each fixed datatype map/vocabulary.
  Origins and anonymous scopes are still caller supplied; duplicate-free nested
  AST materialization, parser provenance and full DL validation remain pending.
- M3 complete Functional Syntax name recognition from bytes: prefix names,
  local names, abbreviated IRIs and node IDs use the referenced SPARQL 2008
  grammar. Actual grammar equivalence, totality, exact acceptance and malformed
  UTF-8 diagnostics are proved; broader Turtle/SPARQL 1.1 escapes are separate.
- M3 actual immutable prefix-table checking and expansion. Every declaration is
  validated, including unused ones; reserved and duplicate names are rejected
  with exact original evidence. The four implicit namespaces, exact lookup,
  preservation of all declaration bytes and complete construction invariant are
  proved. Expansion rechecks both supplied byte parts, bounds the mathematical
  output byte length and validates the final absolute IRI. Exact concatenation,
  all diagnostic phases, termination and acceptance iff the independent grammar,
  lookup, budget and IRI conditions hold are proved. Document punctuation/source
  provenance and full Functional Syntax parsing remain pending.
- M3 generic greedy regular-language prefix recognition at an actual source
  byte position. Exact canonical UTF-8 segments define all eligible endpoints;
  the operation is proved to return their mathematical maximum, with no match
  distinct from an accepted empty prefix. Complete suffix UTF-8 checking,
  first malformed-unit evidence, totality, complete endpoint acceptance and
  source endpoint bounds are proved. The terminal and stream layers are now
  proved separately below.
- M3 complete 2012 Functional Syntax terminal grammars: all 71 keywords, four
  punctuation, seven variable and two special classes. Actual compilation equals
  independent Unicode languages. Quoted strings permit exactly the two OWL
  escapes and retain multiline XML text; language tags use the explicitly named
  RFC 5646 langtag subproduction. Whole-byte recognition and longest matching
  are total and exact. Every eligible token is nonempty and advances within
  source bounds. The actual combined selector visits all 84 classes, returns a
  token iff a valid UTF-8 suffix has a candidate, and chooses a greatest endpoint
  across all candidates. Invalid UTF-8 retains exact first-unit errors. Derived
  keyword/terminal copying is proved exact. The terminal inventory is checked
  against both compiler/specification and full model constructor names. Pairwise
  token-language disjointness and priority-free greatest matching are now proved
  below; separators/trivia are also composed. Other payload
  kinds and full document parsing remain pending. Quoted-string payload
  reading is proved separately below. This stage constructs no
  OWL ontology and executes no OWL inference.
- M3 actual complete quoted-string payload reading. Opening/closing punctuation,
  raw multiline XML text, exactly the two OWL escapes, canonical UTF-8 unit
  concatenation and decoded-output byte budgets have composed totality and
  exact acceptance proofs. Failures preserve first original-unit offsets for
  malformed/truncated input, forbidden XML characters, foreign escapes and
  exceeded budgets. Both directions connect the decoded byte grammar to the
  independent complete quoted-string terminal language; every matching segment
  has a payload, and a fitting budget guarantees the actual exact payload/end
  result. This token reader stops at the closing quote; suffix validation remains
  the separate selector's responsibility. The complete stream lexer is proved
  below. Full document parsing, import composition and OWL validation/reasoning
  remain pending.
- M3 actual whole-source Functional Syntax token streams. Initial strict UTF-8/XML
  checking, complete greatest-token selection with exact inventory priority,
  all seven delimiter characters, greedy discarded whitespace/comments,
  Unicode final-codepoint reading, emitted-token budgets and the whole-document
  loop are composed. Total correctness, complete acceptance in both directions,
  first original source diagnostics and no successful partial stream after a
  later error are proved. Every emitted span is nonempty, ordered, bounded and
  in its independent terminal language; special tokens consume no token budget.
  InvalidSpan is unreachable from the public byte entry point. The separately
  normative assertion that distinct terminal languages never tie is now proved
  below; step-6 special-token prose interpretation is recorded in architecture.md.
  This produces source tokens, not an OWL AST or inference result. Full document
  parsing, other payload construction, import scopes and operational M8 limits
  remain pending.
- M3 complete terminal-language disjointness and priority-free standard selection.
  All 71 keyword spellings are injective, and no two distinct terminal kinds
  accept the same arbitrary Unicode word. Canonical UTF-8 spans with equal byte
  endpoints have equal words, establishing the normative no-ties claim from
  actual source candidates. A greatest-token contract without inventory priority
  is equivalent to the actual selector in both directions and uniquely determines
  kind/start/end. The implemented priority cannot alter any grammar-valid result.
  Proof-only head/colon/final-codepoint classification is derived from independent
  grammars. This closes the disjointness obligation, not full OWL document parsing.
- M3 exact nonnegative decimal payload values from original source spans. The
  actual Rust reader has totality, exact positional-value and both-direction
  acceptance proofs, with first invalid-byte diagnostics and explicit empty/range
  errors. Leading zeroes are accepted; the mathematical Natural value has no
  machine-integer cap. Canonical ASCII spans preserve original byte values;
  complete Functional Syntax integer candidates coincide with valid decimal
  spans. Actual greatest-selected integers and every integer in a successful
  whole-source token stream have the exact value of their source word. This
  constructs integer payloads, not complete cardinality expressions or an OWL
  document. Nonquoted name payloads are proved below; full parsing/import
  integration remains pending.
  Unary values are a research representation; efficient arithmetic, physical
  stack/memory limits and cancellation remain M8 obligations.
- M3 exact nonquoted name payloads from original source spans. Full IRI angle
  markers, node-ID `_:` and language-tag `@` markers are removed; prefix and
  abbreviated names retain their complete original spelling. The actual reader
  revalidates every full terminal span and checks the payload byte budget. Total
  correctness, exact value/acceptance and all error phases in both directions are
  proved. Invalid tokens identify their entire source span start; budget errors
  identify the payload start. Canonical UTF-8 segment/copy equivalence, source
  splitting and the actual returned value grammars are proved, including absolute
  IRIs. Actual greatest-selected names and all five name families in accepted
  complete token streams supply their exact fitting values. No case/percent or
  Unicode normalization occurs. This reader retains abbreviated spelling; the
  source-derived resolver below constructs its expanded IRI. Leading prefix
  declarations and the ontology opening are proved below; remaining header/body
  parsing, roles, scopes and complete AST construction remain pending.
- M3 source-derived full/abbreviated IRI resolution. The actual UTF-8 scan finds
  the syntax colon and constructs exact unchanged prefix/local bytes. Their
  independent grammatical partition is proved unique. Splitting and resolution
  have totality, exact value/acceptance and every error phase in both directions
  proved; internal InvalidParts fallbacks are unreachable. Resolution composes
  exact immutable namespace lookup, final-output budgets and complete absolute
  IRI revalidation. Final limits count returned IRI bytes, so a long source prefix
  can expand under a shorter final limit. Full-IRI budget errors retain the
  payload start; abbreviated expansion errors retain the original token start.
  No spelling normalization occurs. The resolver accepts a checked prefix table;
  the source-derived table stage and composition are proved below. Remaining
  header/body parsing, scopes, full document construction and
  byte-derived imports/provenance remain pending.
- M3 original-byte leading prefix declarations and exact ontology opening.
  The public reader lexes the whole source before syntax/count/value checks,
  reads every leading `Prefix(name=<namespace>)` in source order and returns
  the original `Ontology`/`(` tokens and untouched remaining stream. Declaration
  body shape and payload readers, repeated scanning and the byte entry point
  are proved total. Exact values, full successful acceptance and all syntax,
  declaration-count and payload error phases/offsets are proved in both directions.
  Lexical errors retain the lexer contract; InvalidSpan is unreachable. EOF
  errors retain the original source length; wrong terminals retain their start.
  Count limits precede declaration syntax, then all body syntax precedes prefix
  and namespace payload budgets. Raw duplicate/reserved rows remain present and
  must pass the separately proved normative table constructor. The checked table
  retains exactly the parsed vector; source parsing/checking/IRI resolution have
  composed correctness, exact value and exact error proofs. This is a partial
  parser stage: `Ontology(` may succeed without an ontology body/closing token.
  Ontology/version IRIs and leading imports are proved below. Annotations,
  axioms, scopes and full AST/import assembly remain pending.
- M3 source ontology identity, version and maximal leading-import reading after
  the exact ontology opening. Optional readers consume zero/one/two full or
  abbreviated IRI tokens, retaining original token fields and exact resolved
  values. A version is represented only together with its ontology IRI. Import
  bodies check all three syntax tokens before target resolution; each keyword
  checks the import-count limit before its body. Repeated reading is proved total
  by exact four-token progress and retains source order, repetitions, keyword/IRI
  tokens and the untouched first non-Import or empty suffix. Exact values/suffixes
  and every syntax/resolution/count first error are proved equivalent to independent
  source derivations. Accepted header IRIs satisfy the complete absolute-IRI grammar.
  EOF errors retain original source length, and all other diagnostics retain their
  established source offsets. Actual whole-byte prefix parsing, normative table
  checking and header reading compose using precisely the source-derived namespace
  rows, with checked identity/import values and bounded import count. The low-level
  reader itself receives tokens and a checked table. Unexpected trailing tokens,
  annotations, axioms and final closing syntax remain unparsed, so this is still a
  partial stage. Canonical catalog/closure assembly and scopes/provenance remain
  pending; the existing indexed resolver still receives supplied dependency metadata.
- M3 complete one-literal Functional Syntax source reading. Shapes consume exactly
  one/two/three terminals, preserve every original form token and unchanged suffix,
  and check all written syntax before quote decoding. Arbitrary supplied source
  spans are revalidated. Explicitly typed literals retain exact decoded lexical
  bytes and resolve their original full/abbreviated datatype IRI. Both plain-string
  shortcuts obligatorily expand to rdf:PlainLiteral: payload + '@' + the exact
  language spelling, empty for an untagged string. Final budgets include the added
  separator and the entire constant datatype IRI. Actual source reading is proved
  total; every exact value/suffix and syntax/span/quote/tag/IRI/final-budget error
  is equivalent to an independent first-phase derivation. Quote errors also have
  the complete reverse implication. Exact expansion/spelling laws, both final
  bounds, original quote progress and strict token consumption are checked.
  Whole-byte prefix parsing and normative table checking compose on precisely the
  source namespace rows; the caller still supplies the literal position. Concrete
  datatype lexical/value/facet validation, canonical import/scopes and full
  reasoning remain pending; annotations, axioms and the document model are read by
  the later stages. RDF 1.1 literals keep
  their separately specified representation and syntax conventions.
- M3 Functional Syntax annotations with recursive nesting. The actual reader takes
  the maximal leading `{ Annotation }` sequence in source order, such as the
  ontology annotations after the header. Each annotation may carry nested
  annotations, read one level deeper. Properties and IRI values resolve their
  original spans through the checked prefix table, node IDs keep their exact label
  without `_:`, and literals reuse the proved literal reader. Caller limits bound
  the nesting depth and each sequence's count; errors report the first failing
  phase in source order with original offsets. Totality is proved from token
  progress through both recursive calls. Every exact result and first error is
  equivalent to an independent recursive grammar, and success is equivalent to an
  independent maximal section grammar. Whole-byte prefix parsing, table checking
  and header reading compose on precisely the source namespace rows. Anonymous
  scopes across an import closure remain pending; kernel Annotation values, axioms,
  the closing token and the document model are proved in later stages.
- M3 Functional Syntax entity declarations. The actual reader takes one
  `Declaration( {Annotation} Entity )` axiom at a caller-supplied position, for all
  six entity kinds. Axiom annotations reuse the proved annotation reader and its
  limits; the entity IRI resolves its original span through the checked prefix
  table. Errors report the first failing step in source order with original
  offsets. Totality and exact result/error equivalence to an independent grammar
  are proved; success gives the keyword's exact entity kind, a source-linked IRI,
  the independent annotation section and at least seven consumed tokens. Source
  composition uses the namespace rows parsed from the same bytes. Declaration
  typing remains the existing separate kernel check; the other axiom forms remain
  pending.
- M3 Functional Syntax annotation axioms. The actual reader takes one
  `AnnotationAssertion`, `SubAnnotationPropertyOf`, `AnnotationPropertyDomain` or
  `AnnotationPropertyRange` axiom at a caller-supplied position. Axiom annotations
  and assertion values reuse the proved annotation readers; every IRI resolves its
  original span through the checked prefix table, and node-ID subjects keep their
  exact label. Errors report the first failing step in source order with original
  offsets. Totality and exact result/error equivalence to an independent grammar
  are proved; success gives a body matching the keyword, the independent annotation
  section and at least five consumed tokens. With declarations, this covers every
  non-logical axiom; the other logical axioms remain pending.
- M3 Functional Syntax class expressions and class axioms. The actual readers
  take one class expression of the reasoner's fragment (named classes,
  intersections, unions, complements, enumerations of individuals with
  `ObjectOneOf`, existential and universal restrictions on an object property or
  its `ObjectInverseOf`, and individual value restrictions with
  `ObjectHasValue`), or one `SubClassOf`, `EquivalentClasses`,
  `DisjointClasses`, `DisjointUnion`, `ObjectPropertyDomain` or
  `ObjectPropertyRange` axiom with its annotations, at a caller-supplied
  position. Individuals and individual lists have their own proved reader. The
  other ten class-expression forms are reported as unsupported.
  Nesting depth and member counts have explicit limits. Errors report the first
  failing step in source order with original offsets. The recursive reader is
  proved total by well-founded recursion on the token count, and both readers
  have exact result/error equivalence to an independent grammar. Source
  composition uses the namespace rows parsed from the same bytes. The other
  logical axioms remain pending.
- M3 Functional Syntax assertions. The actual reader takes one `SameIndividual`,
  `DifferentIndividuals`, `ClassAssertion`, `ObjectPropertyAssertion` or
  `NegativeObjectPropertyAssertion` with its axiom annotations at a
  caller-supplied position. Class and object property expressions reuse the
  proved readers; an individual is an IRI resolved through the checked prefix
  table or a node ID with its exact label, and an equality or inequality lists
  at least two. Errors report the first failing step in source order with
  original offsets. Totality and exact result/error equivalence to an
  independent grammar are proved, and every accepted assertion consumes at least
  two tokens. The data property assertions remain pending.
- M3 Functional Syntax object property axioms. The actual reader takes one of the
  eleven object property axioms with its axiom annotations at a caller-supplied
  position: `SubObjectPropertyOf` (whose sub-property may be an
  `ObjectPropertyChain`), `EquivalentObjectProperties`,
  `DisjointObjectProperties`, `InverseObjectProperties` and the seven property
  characteristics such as `TransitiveObjectProperty`. Object property expressions
  reuse the proved reader, member lists and chains need at least two members, and
  errors report the first failing step in source order with original offsets.
  Totality and exact result/error equivalence to an independent grammar are
  proved, and every accepted axiom consumes at least two tokens. Data property
  axioms remain pending.
- M3 Functional Syntax documents. The actual reader takes the original bytes of a
  whole document. It reads the prefix declarations with the proved prefix-header
  reader and checks them with the normative table checker. It then reads the
  ontology identity and imports, the ontology annotations, every axiom up to the
  closing parenthesis, and the end of the source. The axiom loop dispatches on
  all 37 axiom keywords to the proved declaration, annotation-axiom, class-axiom,
  object-property-axiom and assertion readers, reports the other logical axioms as
  unsupported at their
  keyword, and has an axiom count limit. Errors report the first failing stage
  with original offsets. The loop is proved total by token count from each
  reader's minimum consumption, with exact result/error equivalence to an
  independent grammar. Canonical imports and the other axiom forms remain pending.
- M3 the raw OWL model of read documents. The actual kernel mapping turns a read
  document into the raw OWL ontology: the identity, import targets, ontology
  annotations and axioms with their annotations, in source order. IRIs and
  literals keep their exact bytes, node IDs become anonymous individuals of a
  caller-supplied scope, and original tokens are dropped. Assertions keep their
  class expression or property and their named or anonymous individuals,
  enumerations, value restrictions, `SameIndividual` and `DifferentIndividuals`
  their individuals in source order, and object property axioms their
  properties, chains and member lists. Every mapping is proved total, and every
  result corresponds to its source records under an independent structural
  correspondence. The mapping declines only a member list, property chain or
  individual list with fewer than two members or an enumeration without
  members. Independent grammar invariants prove that every such list in an
  accepted document is long enough, so every read document maps.
  Anonymous scopes across an import closure and the other axiom forms remain
  pending.
- Reasoner track, first stage: negation normal form for the ALC fragment. The
  actual kernel translation maps named classes, intersections, unions,
  complements and existential/universal restrictions on named object properties
  to a concept type that admits negation only on named classes; owl:Thing and
  owl:Nothing become top and bottom. It is proved total on all 18 class forms,
  returns no result exactly outside the fragment, and preserves the meaning of the
  expression (or its complement) under the independent Direct Semantics in every
  OWL interpretation, for domains of any universe. The other constructors,
  datatypes and the remaining query reductions remain pending.
- Reasoner track, second stage: a verified ALC tableau for concept
  satisfiability without a TBox. The actual kernel procedure expands conjunctions,
  branches on disjunctions, detects clashes between a named class and its
  negation, and decides each existential restriction together with the universal
  restrictions on its property. It is proved total (well-founded on concept size),
  sound (every acceptance yields an explicit tree model) and complete (a model in
  any universe forces acceptance). With the NNF stage, every rejection proves an
  OWL class expression empty in every OWL interpretation, which justifies
  unsatisfiability and subsumption answers for ALC. This is the first verified
  reasoning procedure in the project and an internal fragment experiment toward
  M6: the remaining SROIQ constructors, datatypes, ontology-level queries and
  performance remain pending.
- Reasoner track, third stage: a verified ALC tableau with a TBox and blocking.
  The actual kernel procedure decides whether some interpretation in which a TBox
  concept holds at every element has an element in a concept. It adds the TBox
  concept at the root and at every successor, and blocks (accepts) a node whose
  literals all occur among the literals of an ancestor. It is proved total (each
  unblocked node adds a new subset of the finite subconcept closure to its branch,
  so branches are bounded by 2^|closure|), sound (every acceptance yields a finite
  Hintikka family of clash-free literal sets whose own interpretation is a model
  of the TBox concept with an instance of the input) and complete (a model in any
  universe forces acceptance). With the NNF stage, every rejection proves an OWL
  class expression empty in every OWL interpretation where the TBox class
  expression holds at every element, which justifies unsatisfiability and
  subsumption answers under ALC general concept inclusions written as that
  expression. Role inclusions and transitive roles are added in the eighth stage
  below; the remaining SROIQ constructors, the other role axioms, datatypes and
  performance remain pending.
- Reasoner track, fourth stage: verified ontology-level ALC queries. The actual
  kernel internalizes an axiom closure into one TBox concept: SubClassOf,
  EquivalentClasses, DisjointClasses, DisjointUnion, and ObjectPropertyDomain and
  ObjectPropertyRange on named object properties, each over ALC class
  expressions; declarations and annotation axioms impose nothing. The
  internalization succeeds exactly on these axioms, and its concept is proved to
  hold at every element exactly when an interpretation fixing owl:Thing and
  owl:Nothing satisfies the whole closure. The queries consistent,
  class_satisfiable and subsumed answer exactly when, in addition, no translated
  concept uses a built-in object property as a role or a built-in class as an
  ordinary named class. Each answer is proved equal to the independent Direct
  Semantics definitions Consistent, ClassSatisfiable and Subsumed for any valid
  vocabulary. Acceptance yields an actual OWL model of the closure: the
  tableau's model gets the fixed built-in classes and object and data
  properties, and data values from the datatype map. Every OWL model, in any
  universe and for any vocabulary, forces acceptance, and a positive subsumption
  answer holds in every such model. Assertions about individuals are added in the
  seventh stage and role axioms in the eighth stage below; the other axiom forms,
  the remaining SROIQ constructors, datatypes, query answering and performance
  remain pending.
- Reasoner track, fifth stage: answers from source bytes. The actual kernel
  functions source_consistent, source_class_satisfiable, source_subsumed and
  (since the seventh stage) source_instance_of read
  a Functional Syntax document from its original bytes, map it into the raw
  model and run the ontology-level query, as one extracted unit. Every call
  terminates. An error is exactly the reader's first error. Every document the
  reader accepts reaches the query: its prefix header is parsed from the same
  bytes, its namespace table passes the normative checker, the independent
  document grammar derives the rest, and its model corresponds to those records.
  The result is the kernel's query on that model's axioms (since the ninth
  stage the SHI queries on the completion graph tableau). No answer therefore
  means the axioms or the query are outside the supported fragment or a `usize`
  limit was reached. An answer is
  proved equal to Consistent, ClassSatisfiable, Subsumed or InstanceOf of the
  read axioms for any valid vocabulary, complete in every universe, and a
  positive subsumption or instance answer holds in every model. The other axiom
  forms, imports, the remaining SROIQ constructors, datatypes and performance
  remain pending.
- Reasoner track, sixth stage: ALC with named individuals. The actual kernel
  procedure abox_satisfiable decides whether some interpretation in which the
  TBox concept holds at every element has an element for every node that
  satisfies given facts (concepts at nodes) and edges (named object properties
  between nodes). The completion adds the TBox concept at every node and each
  fact once. It expands conjunctions, branches on disjunctions and pushes every
  universal restriction's filler along the edges of its role. It then checks
  every node for a clash and decides every existential restriction with the TBox
  tableau, together with the universal restrictions on its role at the same
  node. Termination is proved from the finite set of node and closure pairs.
  Every acceptance yields an explicit model: one element per node and a disjoint
  copy of a successor model for each existential restriction. Every model, in
  any universe, forces acceptance, and the accepting model relates node elements
  only along the given edges. Equality between individuals, inverse roles and
  number restrictions remain pending.
- Reasoner track, seventh stage: ontology queries with assertions. The actual
  kernel queries consistent, class_satisfiable, subsumed and the new instance_of
  now take closures with ClassAssertion, ObjectPropertyAssertion and
  NegativeObjectPropertyAssertion. Every individual an assertion mentions,
  named or anonymous, gets a node by exact structural equality, and node 0
  stands for one further element. A class assertion becomes its translated
  concept at its individual's node and a property assertion an edge along its
  named property; a negative property assertion contradicts the closure exactly
  when the same edge is asserted. Queries put their concepts at node 0 or at the
  queried individual's node and run the completion for named individuals. Each
  answer is proved equal to Consistent, ClassSatisfiable, Subsumed or InstanceOf
  for any valid vocabulary. Every acceptance becomes an OWL model with each
  individual at its node, and every OWL model, in any universe and with any
  reinterpretation of its anonymous individuals, forces acceptance. The answer
  is None outside the fragment, for an assertion on a built-in object property,
  or beyond usize::MAX - 2 individuals. SameIndividual, DifferentIndividuals and
  data assertions remain pending.
- Reasoner track, eighth stage: role inclusions and transitive roles in the TBox
  tableau (SH). The actual kernel procedure satisfiable_with also takes a role
  box: inclusions between named object properties, which must include their
  compositions, and transitive named object properties. A successor along a
  property receives the filler of every universal restriction on a property
  that includes it and, for every transitive property in between, the same
  universal restriction on that transitive property, so elements reached in
  several steps satisfy the filler too. It is proved total (the finite closure
  gains these restrictions), sound (for a role box closed under composition, the
  Hintikka-family model satisfies every listed inclusion and transitivity) and
  complete (every model of the role box, in any universe, forces acceptance).
  The ALC entry points run the same procedure without role axioms and keep
  their theorems. The completion for named individuals takes the same role box:
  a universal restriction reaches the target of every edge whose property it
  includes, together with its restrictions on the transitive properties in
  between, and the accepting model relates node elements exactly as the edges
  and role axioms entail. The ontology queries, also from source bytes, read
  SubObjectPropertyOf between named properties, EquivalentObjectProperties of
  named properties and TransitiveObjectProperty of a named property into a role
  box closed under composition. An interpretation is proved to respect that
  role box exactly when it satisfies those axioms, and the queries decide with
  it. Every answer is proved equal to the Direct Semantics definitions: the OWL
  model of an acceptance reads every other property as the completion's model
  does, so the role axioms hold in it. Role axioms on built-in properties,
  inverse properties or chains in role axioms, the other property axioms and
  negative property assertions together with role axioms get no answer.
  Inverse roles, number restrictions, nominals and property chains remain
  pending.
- Reasoner track, ninth stage: inverse roles. The actual kernel
  translation concepts::translate maps ALCI class expressions, whose
  restrictions may use ObjectInverseOf, to concepts in negation normal form
  whose roles are object property expressions. It is proved total, returns no
  result exactly outside ALCI, and keeps the meaning of the expression (or its
  complement) in every OWL interpretation. hierarchy::RoleHierarchy lists
  inclusions between object property expressions and transitive ones; its
  inclusion and transitivity tests are proved exact. The concept table interns
  concepts as entries whose parts are earlier indices, sharing equal entries;
  interning is proved exact (every index rebuilds its concept), and closing the
  table adds the universal restrictions that transitive roles pass along. The
  completion graph tableau runs on the table: named individuals and trees of
  anonymous nodes, clash detection on insertion, lazy unfolding of `A ⊑ C`, and
  equality blocking. Its rule search is proved exact: it returns what a node
  needs and lacks, else an unblocked node with an unwitnessed existential
  restriction, else Done exactly when no rule applies. completion::satisfiable
  is proved total, sound and complete for SHI with named individuals: an
  acceptance comes with a model of the role hierarchy in which the TBox concept
  and every definition hold everywhere and every fact and link holds, and a
  rejection rules out every such model. The ontology queries in
  shi_ontology run on it: class axioms over ALCI expressions become a TBox
  concept and definitions `A ⊑ C` unfolded lazily, with absorption (`∃r.E ⊑ D`
  as `E ⊑ ∀r⁻.D`, `E ⊓ F ⊑ D` as `E ⊑ ¬F ⊔ D`), domains and ranges of object
  property expressions become universal restrictions, and SubObjectPropertyOf,
  EquivalentObjectProperties, InverseObjectProperties, SymmetricObjectProperty
  and TransitiveObjectProperty on named or inverse properties become a role
  hierarchy proved closed under composition and inverses. Consistency, class
  satisfiability, subsumption and instance checking are proved exact for the
  Direct Semantics in any universes. Negative object property assertions next
  to role axioms, built-in object properties and other constructors get no
  answer. The source-byte queries now run on them, so SHI documents, including
  the full medication-safety example, are answered end to end from their bytes.
- Reasoner track, tenth stage: backjumping and caching. The completion graph
  tableau backjumps: every node records the branch points its label depends
  on, a rule adds to a node with the points of the node and its neighbours, and
  a clash reports the points of its node. When the left disjunct of a branch
  fails without depending on the branch point, the right disjunct is skipped.
  A rejection with clash set D is proved to rule out every model, in any
  universes, that satisfies the labels of the nodes whose points lie in D, so
  satisfiable keeps its exact statement. An inconsistent TBox with eight
  individuals is refuted in milliseconds, where chronological backtracking did
  not finish with three. Reuse across queries: shi_ontology::prepare reads an
  axiom closure once into its individuals, TBox concept and definitions, the
  facts of its class assertions, its closed role hierarchy, its links and
  whether a negative assertion is refuted by a link (PreparedData). The
  prepared queries add only the query's own facts and run the tableau; each is
  proved exact for the Direct Semantics of the closure's axioms in any
  universes. The plain queries are now a preparation followed by the prepared
  query and keep their theorems. source_ontology reads source bytes once and
  never declines a document the reader accepts; source_prepared prepares its
  axioms, proved to give a prepared closure of the bytes' raw OWL ontology. The
  medication-safety example reads its document once for all five questions.
- Reasoner track, eleventh stage: number restrictions. The
  concepts and the concept table now have cardinality restrictions:
  concepts::translate covers ALCIQ (minimum, maximum and exact cardinalities,
  qualified or not, below `usize::MAX`), proved total and exact for the Direct
  Semantics with the OWL counting definitions, and concepts::negate is proved
  to build exact complements. A maximum restriction in the table records the
  complement of its filler; interning is proved to keep that record. The
  completion graph tableau and the ontology queries give no answer when a
  cardinality restriction occurs, so their answers are unchanged. The kernel
  now also has the completion forest (forest.rs), which counts and merges
  nodes: roots for named individuals, trees with lists of roles on their
  edges, merges of tree nodes into siblings, grandparents or named nodes and
  of named nodes into each other, pairwise blocking, and backjumping over the
  choices of which nodes to merge. Its rule search is proved exact
  (forest::next_step and the neighbour lists it counts), and so are the
  operations its rules apply. forest::run is proved to terminate on every
  forest that keeps its invariant: each rule adds a literal to an active node,
  expands a restriction of an unblocked node (pairwise blocking bounds the
  depth) or merges two neighbours, and each decreases a measure. Its
  rejections are proved sound: a rejection rules out every model, in any
  universes, under the branch points it reports, including the backjumping
  over branches and over the pairs a maximum restriction merges.
  forest::satisfiable is proved exact: it answers unless a structure would
  exceed the `usize` range or a number restriction counts along a role that is
  not simple; its true answers come with a model, the unravelling of the
  complete forest under pairwise blocking, of the role hierarchy where the
  TBox concept and every definition hold everywhere and every fact and link
  holds; and its false answers rule out every such model, in any universes.
  The ontology queries now accept number restrictions and functional and
  inverse functional object properties (as `≤1 r.⊤` and `≤1 r⁻.⊤` in the TBox
  concept): a question whose concepts count goes to the forest, and every
  other question to the completion graph tableau as before, both proved exact
  for the Direct Semantics. Negative object property assertions next to a
  question that counts, and number restrictions along roles that are not
  simple, get no answer.
- Reasoner track, twelfth stage: equality and nominals. The
  reader takes `SameIndividual`, `DifferentIndividuals`, `ObjectOneOf` and
  `ObjectHasValue`, and the ontology queries decide individual equalities and
  inequalities. Every member of an equality or inequality gets a node, and
  the members of each `SameIndividual` axiom share the node of a
  representative, computed by uniting classes and proved to be joined to every
  node by a chain of equalities, so every OWL model gives a node and its
  representative one element. Facts, links and the check of negative
  assertions use the representatives' nodes. The completion graph tableau's
  models are proved to keep different named nodes apart, so a
  `DifferentIndividuals` axiom holds exactly unless two of its members share a
  node, which refutes the closure. The concepts and the
  concept table now have nominals `{a}` and their complements, read with the
  individual's OWL meaning: concepts::translate covers ALCIQO, turning an
  enumeration into the union of the nominals of its individuals and a value
  restriction into `∃r.{a}`, proved exact for the Direct Semantics. The
  completion graph tableau gives no answer when a nominal reaches a label. The
  completion forest has the nominal rule: a named node, or a child of one,
  whose label has `{a}` is merged into the named node of `a` (the node of the
  first requirement with `{a}`), and a difference between them is a clash.
  Every model places both on `a`, so the rejections stay sound, and the model
  of a complete forest places each individual on the path of its named node,
  so the acceptances stay exact. A nominal below a tree node, or an individual
  of a nominal or its complement without a named node, gets no answer. The
  ontology queries take nominals of named individuals: the individuals of the
  nominals of a closure get nodes, and a question with a nominal, one that
  counts, or one about a closure with negative assertions next to role axioms
  goes to the completion forest, which also gets the nominal `{a}` of every
  individual at its node, every inequality as its members outside the
  nominals of the later members, and every negative assertion `¬r(a, b)` as
  `∀r.¬{b}` at `a`. These facts are proved to hold in every OWL model of the
  closure, and the forest's model, with every individual where its nominal is,
  is proved to give an OWL model of the closure, so the answers stay exact;
  inequalities and negative assertions next to counting or role axioms are now
  decided. A nominal of an anonymous individual, or in a question of an
  individual the closure does not have, gets no answer.
- Reasoner track, thirteenth stage: nominals anywhere. The completion
  forest's nominal rule now merges a node with `{a}` at any depth
  into the named node of `a`: the parent of a merged tree node, a named or a
  tree node, gets an added edge to the named node, and the added edges of the
  merged node move to the named node. Added edges count only from live nodes
  (active and not blocked), and pairwise blocking only repeats tree nodes with
  a tree parent, so the model of a complete forest relates every path of a live
  tree node with an added edge to the path of the named node, and the truth
  lemma is proved for these edges. Named nodes are no longer tied to
  individuals, and a merged named node hands its added edges on to its target.
  Since the model may repeat such a tree node, a maximum restriction `≤n r.C`
  of a named node must not count it: the forest then guesses the number of
  neighbours along `r` that satisfy `C`, from 1 to `n`, and creates that many
  new named nodes with the seed `C`, an added edge from the node and the guess
  as a bound; with the bound, the tree node is merged with one of the counted
  named neighbours. Every model of the restriction has an exact number of such
  neighbours, so the guesses are proved complete with backjumping, and a
  measure that weights every restriction without a bound by the index of its
  node, the earlier the heavier, proves that the run still terminates. Value
  restrictions, enumerations and counting through nominals of named
  individuals below anonymous elements are now decided by the forest and the
  ontology queries; every random input of the tests with such nominals is
  answered. No answer remains only when a bound has fewer counted named
  neighbours than it allows, which the tests never reach.
- Reasoner track, fourteenth stage: SROIQ role features. The
  concepts and the concept table have self restrictions `∃r.Self` and their
  complements, which hold exactly at the elements that `r` relates to
  themselves, or not: concepts::translate covers `ObjectHasSelf`, proved exact
  for the Direct Semantics. The completion forest reads a self restriction
  `∃s.Self` of a node as a loop, an edge from the node to itself along `s`: the
  node is its own neighbour along every role that includes `s` or its inverse,
  universal restrictions pass along the loop, and a node with `¬∃r.Self` that
  is its own neighbour along `r`, through a loop, a link or an added edge, is a
  clash. The model of a complete forest relates a path to itself along the
  loops of its newest node, and complements of self restrictions, like number
  restrictions, must be on simple roles, so the truth lemma covers both. The
  ontology queries now take `ObjectHasSelf` and reflexive and irreflexive
  object properties (as `∃r.Self` and `¬∃r.Self` in the TBox concept) and
  decide them with the forest. A loop can make a maximum restriction merge a
  tree node into its own parent: the edge between them then becomes loops of
  the parent, whose self restrictions the table has for the role of every
  existential and minimum restriction. The tests answer every one of 300
  random inputs with self restrictions and reflexive, irreflexive and
  functional properties. Asymmetric and disjoint object properties become
  disjoint pairs of the role hierarchy, an asymmetric property paired with its
  inverse: a node with one neighbour along both roles of a pair is a clash,
  the model of a complete forest keeps every pair apart, and the pairs must be
  on simple roles. The ontology queries take both axioms and decide them with
  the forest.
- Reasoner track, fifteenth stage: role chains. Complex role inclusions
  `r1 ∘ … ∘ rn ⊑ r` are decided by an encoding in front of the completion
  forest: every complex role (one that the role of a chain is included in) has
  an automaton of its chains, a universal restriction on it becomes a fresh
  class for the automaton's initial state, and every such class gets a
  definition that passes its filler along the automaton's transitions.
  role_chains::satisfiable answers as forest::satisfiable with the chains as
  further role axioms: its acceptances come with a model of the hierarchy, the
  chains and the disjoint pairs, built by closing the forest's model under the
  role axioms, and its rejections rule out every such model, since each model
  of the chains is one of the encoding once every fresh class holds where its
  automaton leads into its filler. The ontology queries read every
  `SubObjectPropertyOf` with an `ObjectPropertyChain` as a role chain, proved
  exact against its Direct Semantics, and route every closure with chains to
  the forest, also from Functional Syntax source bytes. Number restrictions,
  self restrictions and disjoint pairs must be on roles that no chain reaches,
  as OWL 2 requires simple roles there, and a hierarchy whose automata would
  nest themselves, which only an irregular one does, gets no answer.
- 1648 audited public theorems and 906 audited semantic definitions. Consistency,
  class satisfiability, subsumption and instance checking are decided, with
  proofs against the OWL definitions, for axiom closures whose logical axioms are
  ALCIQO class, domain and range axioms with number restrictions on simple
  roles, nominals of named individuals and self restrictions, functional,
  inverse functional, reflexive, irreflexive, asymmetric and disjoint object
  properties, class, object property and negative object property
  assertions, individual equalities and inequalities, and inclusions,
  equivalences, inverses, symmetry, transitivity and chains of object property
  expressions (SROIQ without the universal and empty roles), also directly from
  Functional Syntax source bytes.
  No full OWL decision procedure is proved yet. See m3-m4-progress.md for the
  input contracts.
- 456 Rust regression tests, plus a separately fetched 68-case W3C syntax corpus;
  maintenance OWL/RDF examples, a medication-safety example answered from its
  bytes, and CLI status/demo/check-nt/export-nt commands. The SHI queries use
  lazy unfolding with absorption, clash detection on insertion, equality
  blocking and backjumping, the queries that count or have nominals a
  completion forest with pairwise blocking and backjumping over merges, and a
  closure or document
  prepared once answers any number of queries.
- Exact-source linkage covering Rust, proof sources and audit/inventory gates.
  The frontend stages are extracted together with the kernel as one Lean
  development, so parsing and reasoning can be composed without assumptions;
  `rowl-frontend` re-exports them.
  Extraction rejects unknown external axioms/opaque declarations. Every public
  project theorem is audited; allowed logical axioms remain only propext,
  Classical.choice and Quot.sound.
- A 1841-obligation release ledger and separate checked constructor and built-in inventories.
  M2 representation entries and narrow M3/M4 proof obligations are covered;
  broad frontend/validation/reasoning requirements remain pending.

The maintenance example constructs four raw axioms: machines with a faulty part
need inspection; pump1 is a machine; pump1 hasPart motor1; motor1 is faulty.
Rowl.Owl.maintenance_follows proves the consequence for any interpretation
satisfying those premises. The executable constructs the ontology and describes
that theorem. It also actually checks the declarations, demonstrating the missing
FaultyPart diagnostic and a successful repair, then rejects reusing `owl:Thing`
as an object property despite its allowed generic class/property punning. It
does not automatically perform OWL inference. It also accepts faultCode as a
subproperty of owl:topDataProperty, then detects trying to make that top property
functional using the proved occurrence checker. The simple-role example rejects
a cardinality restriction on transitive hasPart and accepts after transitivity
is removed. The chain example finds a valid order for hasPart/hasPart-to-nestedPart,
then rejects adding the reverse nestedPart-to-hasPart hierarchy edge. Both run
the Rust validators, rather than merely describing a semantic consequence.

## Proof boundary

M1 and the new M3/M4 component proofs connect actual Rust operations to
mathematical specifications. M2 supplies the full declarative specification and
checked laws. The UTF-8/XML character component is proved from bytes. Catalog/import
and typing metadata has not yet been fully derived/assembled from serialized
OWL/RDF bytes; the new Functional Syntax stage derives identity/import IRI
references, while full document parsing and catalog composition remain pending. The
symbol table and raw-ontology checker operate directly on byte-buffer IRIs,
without an unproved String conversion, but do not invoke lexical validation; a separate IRI byte entry point is now
proved sound/complete against RFC 3987. The UTF-8 encoder and complete language-tag recognizer are also proved.
The N-Triples token subpipeline now includes composed byte-to-blank-token
correctness and complete acceptance, exact trivia/span-copy proofs and full
quoted-token, IRIREF, language/literal/object/triple and bounded whole-document
composition. Public reading is proved from bytes to exact raw graph occurrences
under its stated term/count limits. The writer, canonical import scope assignment,
RDF-to-OWL mapping and full byte-to-ontology pipeline remain unproved. Correspondence to W3C prose/tables is
a reviewed specification choice, not a mechanical proof of English. See
m2-semantics.md for the mapping.

Functional Syntax now also has a source-derived leading-prefix/ontology-opening
stage with complete byte acceptance and exact source payloads. Raw declaration
syntax alone does not establish a valid namespace table: the separate checked
constructor enforces reserved names and duplicates. The composition theorems
connect that exact source table to IRI value/error contracts. The following
ontology/version identity and maximal leading imports also have source-derived
value/error composition proofs. Ontology annotations, including nested ones,
now have source-derived value/error composition proofs as well, and so do single
entity declarations, annotation axioms, ALC class expressions and class, domain
and range axioms, and whole documents of those axioms with their closing syntax
and end of source. The other logical axioms are reported as unsupported. Read
documents map into the raw model with a proved exact correspondence, and the ALC
queries compose with the reader and the mapping from the original bytes;
canonical catalog/import construction remains pending.

Datatype maps are explicit parameters with their stated laws, not an assumed
external solver. The concrete normative OWL map is unimplemented. Semantic
predicates extend to raw terms; release callers must first establish lexical
validity, vocabulary membership, canonical structure and DL restrictions.
No ValidatedOntology or definitive OWL-query entry point exists yet.

No sorry, admitted project claim or custom semantic axiom is accepted. Pinned
compiler/translation tools, primitive library models, Lean and its normal logical
axioms remain the documented trusted computing base. Physical memory/stack
exhaustion is not eliminated by mathematical termination; typed resource and
cancellation outcomes remain M8 work.

Local verification covers formatting, Clippy with warnings denied, all Rust
tests, actual-source regeneration/comparison, Lean builds and axiom audits.
The expanded CI workflow exists locally; no hosted CI run is claimed.

## Next milestones

1. M3: verified Functional Syntax and standard RDF graph/dataset parsing, export
   laws and canonical mapping (see `formats.md`);
   connect the proved indexed closure to document IRIs, headers, declarations,
   RDF includes, anonymous scopes and provenance.
2. M4: finish structural/global DL
   validation, normalization and role preprocessing, then compose the components.
3. M5–M7: normative datatypes, SROIQ tableau and full OWL integration.
4. M8–M9: queries, replayable evidence, operational outcomes and byte-to-answer
   composition before the full OWL 2 DL v0.1 release.

The maintenance example also runs the composed anonymous checker. An unknown
assembly attached to two named pumps passes when its anonymous motor has no
named attachment and supplies a qualifying component root. Attaching that motor
to both pumps leaves no root and returns NoBoundaryRoot. This demonstrates the
literal normative boundary condition; the informative example discrepancy is
recorded in architecture.md. The combined checker completes the anonymous
restrictions block, not the whole M4 milestone.
