# Implementation status

M0, M1 feasibility probes and M2 structural representation/independent semantics
are complete. M3 and M4 have verified components; both milestones remain in
progress. Functional Syntax, Turtle, N-Triples and RDF/XML documents are read,
and SROIQ with nineteen datatypes is decided, with proofs (below); a decision
procedure for all of OWL 2 DL, its other datatypes and facets and the other
formats are future work.

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
  diagnostics. Its import metadata now comes from document bytes (next item).
- M3 import catalogs from document bytes (`import_catalog`). Every document of a
  caller-supplied catalog (Functional Syntax, N-Triples or Turtle bytes; nothing
  is fetched) is read by its verified reader, with its node IDs or blank nodes in
  a scope of its own, the eight bytes of its position; whatever reading returns
  is proved to be the reader's result, and Functional Syntax catalogs are proved
  to be read (the reverse RDF mapping has no termination proof). An import IRI
  names the documents whose ontology IRI or version IRI it is (§3.2, §3.4),
  decided exactly; `lookup` reports none, exactly one or the first two of
  several. The catalog for `imports::resolve` has exactly the direct imports as
  edges and the §3.4 import closure as reachability. RDF documents are still
  read without the declarations of the documents they import.
- M3 import closures and their axiom closures (`import_closure`). From the read
  catalog, `assemble` resolves the import closure of a root document with the
  proved `imports::resolve`; the first import IRI of a closure document that
  names no document or several is a typed error with the document and the IRI,
  and imports of documents outside the closure do not matter. Every anonymous
  individual of a closure document is checked to have its document's scope
  (`anonymous_scopes`, decided exactly; for Functional Syntax documents the
  check is proved never to fail), and the closure holds the root's
  identity and imports and the ontology annotations and axioms of the closure
  documents in catalog order, every axiom with its document and position. The
  assembly is proved total and exact, the assembled axioms are proved to have
  exactly the models of the import closure, each document's anonymous
  individuals interpreted on their own, and hence its consistency, entailment,
  satisfiability, subsumption and instances, and every axiom is proved to be the
  one at its recorded origin. The imported documents' ontology and version IRIs
  are not checked against the reserved vocabulary.
- Import closures in the reasoner: `Reasoner::from_documents` reads the import
  closure of a root document from a catalog with the verified `source_closure`
  and reasons over its axiom closure; missing and ambiguous imports are errors
  naming the document and the IRI. The CLI's `check`, `classify`, `instances`
  and `validate` take `--imports DIR` (every `.ofn`, `.nt` and `.ttl` file of the
  directory joins the catalog), the C interface has
  `rowl_reasoner_from_documents` and Python `Reasoner.from_file(path,
  imports=...)` and `Reasoner.from_documents`. `dl_violation` then checks the
  whole closure, imported declarations included, and names an offending axiom's
  document. RDF documents are read with their own declarations only.
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
  fragments. RFC 3986 reference resolution is proved below; ontology integration
  remains pending. Functional Syntax prefix expansion is separately proved below. Since the compiled-grammar stage
  the validators compile the grammar into a node table and match by partial
  derivatives over continuation stacks; that matcher is proved to return the
  derivative matcher's result, so the statements above are unchanged. IRIs of
  the plain form `scheme://host/segment…#fragment` with ASCII letters, digits,
  `-`, `.`, `_` and `~` are accepted by a byte scan without building the
  grammar, proved to accept only well-encoded IRIs.
- M3 RFC 3986 section 5.2 reference resolution on the UTF-8 bytes of IRIs:
  Appendix B splitting, the strict transformation with path merging and
  dot-segment removal, and recomposition. `references::resolve` is proved to
  compute exactly the algorithm as written from the RFC in `IriResolution.lean`
  on inputs shorter than `usize::MAX / 8` bytes, and the algorithm to commute
  with UTF-8. Resolving an IRI reference against an IRI is proved to give an IRI
  with the RFC target components whenever the target has an authority or a path
  not beginning with `//`; a proved counterexample shows that the RFC algorithm
  can leave the IRI grammar otherwise. `references::is_reference` is proved to
  accept exactly the UTF-8 spellings of RFC 3987 IRI references.
- M3 XML 1.0 and Namespaces in XML 1.0 reading for RDF/XML (`xml::read`):
  strict UTF-8 with a leading byte order mark dropped and line ends normalized,
  the XML declaration, comments, processing instructions, a document type
  declaration whose internal subset declares entities, elements, attributes
  normalized as §3.3.3 prescribes, character data, CDATA sections, character
  and entity references under an expansion budget, and namespace resolution
  under every namespace constraint. Proved against an independent grammar over
  code points: when the byte length plus the budget fits in `usize`, `read`
  returns the element tree exactly for the supported documents, that tree is
  unique, and every other input gives a typed error. Other encodings, element
  type, attribute-list and notation declarations, parameter-entity references
  and external or unparsed entities are declined.
- M3 RDF/XML reading (`rdfxml::read_with_limits`, `rdfxml::graph`): RDF 1.1 XML
  Syntax over the element trees of `xml::read`, with element and attribute
  events, `xml:base` resolved by RFC 3986 section 5.2, `xml:lang`, node elements
  with `rdf:ID`, `rdf:nodeID`, `rdf:about` or generated blank nodes, typed node
  elements, property attributes, resource, literal, `parseType="Resource"`,
  `parseType="Collection"` and empty property elements, `rdf:li`, reification by
  `rdf:ID` with its uniqueness constraint, and blank nodes in a caller-supplied
  scope. Proved against independent relations for sections 5 to 7: `graph`
  returns exactly the triples, in order, that the grammar derives within the
  term and item limits, and an error exactly when it derives none; from bytes,
  `read_with_limits` returns a graph exactly when the XML grammar reads a tree
  that has one, with those triples. `rdf:parseType="Literal"` is declined with a
  typed error, since XML literals need XML canonicalization. Catalogs read
  RDF/XML documents through `import_catalog::read_source` with `rdfxml_limits`
  (an entity expansion budget and term limit of 2^24, at most `usize::MAX / 2`
  triples), proved by `read_source_correct` against the XML and RDF/XML
  grammars, and `Reasoner::from_rdfxml`, the CLI (`.owl` and `.rdf` files,
  relative IRIs resolved against the file's `file:` IRI), the C interface and
  Python read RDF/XML through it. The W3C RDF/XML evaluation and negative cases
  pass except the three with XML literals. XML decoding is a loop; element
  content recurses once per sibling (about 1.6 KB of stack each), which the
  4 GiB kernel stack bounds to documents of a few hundred MB.
- M3 compiled regular grammars. `compiled::compile` turns an expression into a
  table of nodes whose parts come before them, and the matcher keeps a state of
  continuation stacks of node indices, so it never copies the grammar. Against
  an independent reading of the table, compiling gives the root the
  expression's language and keeps every empty-word flag right; every matching
  step replaces the state's language by the words that remain after the
  consumed code point. `matches` therefore returns exactly `matches_utf8`'s
  result, malformed UTF-8 included, and on a valid suffix `longest_valid`
  returns exactly `longest_prefix`'s result. A table or state beyond the
  `usize` range is reported, and the callers then use the derivative matcher.
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
  malformed suffix can expose a successful partial graph. Export is proved below.
- N-Triples read and export with strict UTF-8, absolute IRIs, escaped
  lexical forms, well-formed tags, exact datatype spelling, scoped blank keys,
  comment/line handling and count/byte budgets. All 68 official W3C syntax
  cases pass, and positive cases round-trip through the writer with an
  independent blank-bijection/term-preservation check. See formats.md.
- M3 N-Triples and Turtle writers proved by round trips: `RdfWrite.lean` gives
  the written text and the terms each syntax cannot carry as Lean functions of
  the graph, and `ntriples_write_total_correct` and `turtle_write_total_correct`
  prove that the writers return exactly that text within the byte budget, the
  first such term, or the exhausted budget. `ntriples_write_read` and
  `turtle_write_read` prove that the verified readers read the written bytes back
  as the graph's triples in order, with blank nodes renamed one to one into the
  reader's scope (Turtle against any base shorter than `usize::MAX / 8` bytes).
  `ntriples_write_error_exact`: when the N-Triples writer reports a term it
  cannot carry, no N-Triples document denotes the graph up to blank nodes. The
  Turtle writer is a canonical subset without prefixes; it also rejects IRIs that
  RFC 3986 resolution changes, which Turtle could carry through prefixed names.
- M3 RDF 1.1 Turtle byte-to-graph reading: the whole grammar of section 6.5
  (`@prefix`/`@base` and SPARQL directives, prefixed names with local escapes,
  blank node property lists, collections, object and predicate-object lists and
  every literal form) with longest-match tokens, RFC 3986 resolution of relative
  IRIs against the base in force, RFC 3987 IRI and BCP 47 tag checks, generated
  blank nodes labelled from byte offsets in the caller's scope and the triple
  order of section 7. Every token and production reader has totality and
  complete-acceptance proofs against independent relations;
  `read_with_limits_total_correct` and `read_with_limits_accepted_iff` prove that
  `turtle::read_with_limits` returns exactly the triples a document denotes, in
  order, or its first error, and a graph exactly for Turtle documents within the
  limits. All 313 W3C RDF 1.1 Turtle cases pass. The reasoner, the CLI and the
  Python package read the OWL ontologies of Turtle graphs through the RDF
  mapping below; Turtle export, in a canonical subset, is proved above.
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
  The named-boundary condition is proved separately below; per-document scopes are assigned when an import closure is read (`import_closure`).
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
  normalization. It takes the supplied complete standardized-apart closure, which
  `import_closure` now assembles from document bytes.
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
- M4 composed OWL 2 DL validity. `dl_validity::check_ontology` checks the
  supplied axioms, taken as the complete axiom closure, against the OWL 2 DL
  conditions of Structural Specification Section 3 in that order: nonempty keys
  and structural arities, the reserved vocabulary in headers and entity
  positions, the typing constraints with the built-in declarations, and the
  §11.2 restrictions on `owl:topDataProperty`, datatypes, simple roles, the
  property hierarchy and anonymous individuals. `OwlDlValid` is the
  conjunction of the components' independent specifications; the check is
  proved to return `Valid` exactly for it, and otherwise the first violation
  with its component evidence and every earlier restriction proved. The typing
  stage decides the typing predicate on exact IRI spellings without a symbol
  limit, finding declarations through a hashed index of their positions, and
  agrees with the symbol-indexed checker. Declaration consistency (§5.8.2)
  is decided separately, the built-in vocabulary restrictions and punning are
  characterized, and annotations are proved to have no logical effect on
  models, consistency and entailment. The lexical forms of literals (§5.7) and
  facet values (§7.5) are not checked; the check takes the axioms it is given,
  which for an import closure are those `import_closure` assembles. `Reasoner::dl_violation`,
  the CLI's `validate` command, the C interface's `rowl_dl_violation` and the
  Python `Reasoner.dl_violation()` report this verdict for a loaded document
  or import closure in words, computed when asked; loading never rejects a
  document for it.
- M3 complete Functional Syntax name recognition from bytes: prefix names,
  local names, abbreviated IRIs and node IDs use the referenced SPARQL 2008
  grammar. Actual grammar equivalence, totality, exact acceptance and malformed
  UTF-8 diagnostics are proved; broader Turtle/SPARQL 1.1 escapes are separate.
  Prefix names, local names and abbreviated IRIs that an ASCII scan reads whole
  are accepted without matching the grammar, with the same theorems. Full IRIs
  `<…>` end at the first `>` byte and are validated once as RFC 3987 IRIs.
- M3 actual immutable prefix-table checking and expansion. Every declaration is
  validated, including unused ones; reserved and duplicate names are rejected
  with exact original evidence. OWL 2 forbids declaring the four standard
  prefix names `rdf:`, `rdfs:`, `xsd:` and `owl:` (Structural Specification,
  §3.7), but tools built on the OWL API, Protégé among them, write a
  declaration for each with its own namespace. The reader accepts exactly such
  a restatement, which changes no expansion, and rejects any other namespace
  for these names (`Rowl.Prefixes.Reserved`). The four implicit namespaces, exact lookup,
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
  remain pending. Since the lexer performance stage, each token is selected on
  the validated text by matchers that stop once no longer match is possible,
  and only for terminals whose words can begin with the next code point
  (prefix names and abbreviated IRIs only at `:`, ASCII letters and code points
  outside ASCII); both shortcuts are proved equal to the standard greatest
  selection. Prefix names and abbreviated IRIs are first scanned over ASCII
  bytes without their grammars, and full IRIs up to their first `>` byte;
  whenever the scanners answer, the answer is proved to be the greatest
  candidate endpoint of the independent languages.
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
  non-logical axiom.
- M3 Functional Syntax class expressions and class axioms. The actual readers
  take one class expression of the reasoner's fragment (named classes,
  intersections, unions, complements, enumerations of individuals with
  `ObjectOneOf`, existential and universal restrictions on an object property or
  its `ObjectInverseOf`, individual value restrictions with `ObjectHasValue`,
  self restrictions with `ObjectHasSelf`, and `ObjectMinCardinality`,
  `ObjectMaxCardinality` and `ObjectExactCardinality` with or without a filler),
  or one `SubClassOf`, `EquivalentClasses`, `DisjointClasses`, `DisjointUnion`,
  `ObjectPropertyDomain` or `ObjectPropertyRange` axiom with its annotations, at
  a caller-supplied position. Individuals and individual lists have their own
  proved reader. The number of a number restriction is read by a proved bounded
  decimal reader: its value is at most the count limit, and a larger number is
  rejected at its token without forming its value. The six data restrictions
  (`DataSomeValuesFrom`, `DataAllValuesFrom`, `DataHasValue` and the data number
  restrictions) take one data property, since every OWL 2 data range is unary,
  with literals read by the proved literal reader and data ranges by the proved
  data range reader: datatypes, `DataIntersectionOf`, `DataUnionOf`,
  `DataComplementOf`, `DataOneOf` and `DatatypeRestriction` with its facets. All
  eighteen class-expression forms are read.
  Nesting depth, member counts and numbers have explicit limits. Errors report the first
  failing step in source order with original offsets. The recursive reader is
  proved total by well-founded recursion on the token count, and both readers
  have exact result/error equivalence to an independent grammar. Source
  composition uses the namespace rows parsed from the same bytes.
- M3 Functional Syntax assertions. The actual reader takes one `SameIndividual`,
  `DifferentIndividuals`, `ClassAssertion`, `ObjectPropertyAssertion`,
  `NegativeObjectPropertyAssertion`, `DataPropertyAssertion` or
  `NegativeDataPropertyAssertion` with its axiom annotations at a
  caller-supplied position. Class and object property expressions and literals
  reuse the proved readers; an individual is an IRI resolved through the checked
  prefix table or a node ID with its exact label, and an equality or inequality
  lists at least two. Errors report the first failing step in source order with
  original offsets. Totality and exact result/error equivalence to an
  independent grammar are proved, and every accepted assertion consumes at least
  two tokens.
- M3 Functional Syntax object property axioms. The actual reader takes one of the
  eleven object property axioms with its axiom annotations at a caller-supplied
  position: `SubObjectPropertyOf` (whose sub-property may be an
  `ObjectPropertyChain`), `EquivalentObjectProperties`,
  `DisjointObjectProperties`, `InverseObjectProperties` and the seven property
  characteristics such as `TransitiveObjectProperty`. Object property expressions
  reuse the proved reader, member lists and chains need at least two members, and
  errors report the first failing step in source order with original offsets.
  Totality and exact result/error equivalence to an independent grammar are
  proved, and every accepted axiom consumes at least two tokens.
- M3 Functional Syntax data property axioms, datatype definitions and keys. The
  actual reader takes one `SubDataPropertyOf`, `EquivalentDataProperties`,
  `DisjointDataProperties` (at least two data properties), `DataPropertyDomain`,
  `DataPropertyRange`, `FunctionalDataProperty`, `DatatypeDefinition` or `HasKey`
  (a class expression and two parenthesized lists of object and data properties)
  with its axiom annotations at a caller-supplied position, reusing the proved
  class-expression, object-property and data-range readers. Errors report the
  first failing step in source order with original offsets; totality, exact
  result/error equivalence to an independent grammar and progress are proved.
- M3 Functional Syntax documents. The actual reader takes the original bytes of a
  whole document. It reads the prefix declarations with the proved prefix-header
  reader and checks them with the normative table checker. It then reads the
  ontology identity and imports, the ontology annotations, every axiom up to the
  closing parenthesis, and the end of the source. The axiom loop dispatches on
  all 37 axiom keywords to the proved declaration, annotation-axiom, class-axiom,
  object-property-axiom, data-axiom and assertion readers, so every axiom form is
  read, and has an axiom count limit. Errors report the first failing stage
  with original offsets. The loop is proved total by token count from each
  reader's minimum consumption, with exact result/error equivalence to an
  independent grammar. Import closures are assembled by `import_closure`.
- M3 the raw OWL model of read documents. The actual kernel mapping turns a read
  document into the raw OWL ontology: the identity, import targets, ontology
  annotations and axioms with their annotations, in source order. IRIs and
  literals keep their exact bytes, node IDs become anonymous individuals of a
  caller-supplied scope, and original tokens are dropped. Assertions keep their
  class expression or property and their named or anonymous individuals,
  enumerations, value restrictions, `SameIndividual` and `DifferentIndividuals`
  their individuals in source order, number restrictions their numbers as
  unary naturals and their fillers, data restrictions their data properties,
  literals and data ranges, object property axioms their properties, chains and
  member lists, and data property axioms, datatype definitions, keys and data
  assertions their data properties, class expressions, data ranges, literals
  and individuals. Every mapping is proved total, and every
  result corresponds to its source records under an independent structural
  correspondence. The mapping declines only a member list, property chain or
  individual list with fewer than two members or an enumeration without
  members. Independent grammar invariants prove that every such list in an
  accepted document is long enough, so every read document maps.
  Anonymous scopes across an import closure are assigned by `import_closure`.
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
  stage the SHI queries on the completion graph tableau, now the data queries
  of `data_ontology`). No answer therefore means the axioms or the query are
  outside the supported fragment or a `usize` limit was reached. An answer is
  proved equal to Consistent, ClassSatisfiable, Subsumed or InstanceOf of the
  read axioms for any valid vocabulary under every datatype map that is the OWL
  2 map on the datatypes of `datatypes::literal_value`, and a positive
  subsumption or instance answer holds in every such model. Imports, the other
  facets, datatype definitions, keys with a data property, data ranges of the
  other datatypes and performance remain pending.
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
  equality blocking (since the anywhere-blocking stage by any earlier unblocked
  tree node with the same label, not only by one on the node's own path). Its
  rule search is proved exact: it returns what a node
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
  Since the prepared-base stage, preparing also interns the facts, the TBox
  concept and the definitions into a closed concept table once
  (`completion::base`, described by `BaseFor`); a query that goes to the
  completion graph tableau copies that table, interns only its own facts and
  closes the copy again (`completion::satisfiable_from`), with exactly the
  guarantees of `satisfiable` on the base's inputs. On a generated 400-class
  ontology the per-query table setup fell from 3.7 ms to 0.2 ms.
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
- Reasoner track, sixteenth stage: the universal and empty roles. The empty
  role `owl:bottomObjectProperty` is an ordinary role for the tableaux, and the
  TBox concept also conjoins `∀B.⊥` for it, so it relates nothing in their
  models, as OWL requires: the ontology queries take it in every position, in
  concepts, inclusions, chains, characteristics and assertions. The universal
  role `owl:topObjectProperty` relates every pair, so a restriction `∃U.C` or
  `∀U.C` along it holds at every element or at none: a question that uses it
  goes to the completion forest over the guesses for the truths of these
  restrictions (`universal`), each made good by a further element or by the
  TBox concept, and a model of one guess, with the universal role then relating
  every pair, is a model of the question, while every OWL model is a model of
  the guess of its own truths. Inclusions and chains into the universal role,
  its symmetry and transitivity, and assertions along it are taken as they are.
  This completes SROIQ: no number restriction may count along the universal
  role, as OWL 2 DL requires, and it is never included in another role.
- M5 datatype values: an independent specification of the OWL 2 datatype map on
  `xsd:integer`, `xsd:decimal`, `xsd:string`, `rdf:PlainLiteral` and
  `xsd:boolean` (Rowl.DatatypeMap.Normative), with their XML Schema lexical
  spaces, lexical-to-value mappings and value spaces, and a model map that
  satisfies it. The actual `datatypes::literal_value` returns a canonical value
  exactly for a literal of these datatypes in its lexical space; under every
  normative map that is the literal's value, equal values are equal kernel
  values (`1`, `+01` and `1.000` are one), and datatype membership is exact.
- M5 numeric datatypes and range facets on single values: Normative also
  specifies `owl:real` (the reals, no literals), `owl:rational` (the rationals,
  lexical forms `numerator/denominator`), and the twelve subtypes of
  `xsd:integer` with their XML Schema bounds, and the facets `xsd:minInclusive`,
  `xsd:maxInclusive`, `xsd:minExclusive` and `xsd:maxExclusive` (facet spaces
  and facet values from OWL 2 §4.1 and XML Schema 1.1); a model map over the
  reals satisfies it. Numbers can denote reals: Normative has an injective
  `real` embedding whose restriction to the rationals is the number embedding.
  `literal_value` reads literals of all nineteen datatypes, `owl:rational` ones
  into fractions in lowest terms, the kernel orders numbers exactly by
  arithmetic on decimal digit strings (`numbers`, Rowl.Numbers) and evaluates
  the four facets on a number exactly (`compare_values_correct`,
  `facet_holds_correct`, `normative_facet`, `facet_applies_correct`).
  OwlSemantics' DatatypeMap no longer has the field `facetInSpace`, which read
  literally contradicts Table 4 for `owl:real` (see m3-m4-progress.md).
- M5 numeric data ranges and range facets in the ontology queries: data ranges
  of `owl:real`, `owl:rational` and the twelve integer subtypes, and datatype
  restrictions of every numeric datatype by the four range facets with numeric
  bounds, are answered inside data restrictions, ranges, intersections, unions,
  complements and enumerations. The bounds of facets and subtypes become cuts
  of the real line that the kernel orders and counts exactly (`regions`,
  Rowl.Regions); each cut gets a class, chained in order, each numeric literal
  value's individual is in exactly the classes of the cuts that contain its
  number, the two cuts of a number leave only its literal value's individual,
  and between neighbouring cuts of different numbers the integers that are no
  literal values are none or at most their number at any element along a role
  `U` above every data property, when they are fewer than a capacity that
  bounds the counts of the data restrictions of the closure and its questions
  (`region_axioms_spec`, `class_count_spec`, `items_count_spec`). An OWL model
  lifts to a model of the encoding (`lifted_regions`), and a model of the
  encoding gives an OWL model whose data nodes take values from the region
  between their cuts at their level (integers, decimals, rationals or
  irrational numbers), without the numbers of the literal values: infinite, or
  a bounded run of integers that holds an element's values by the axiom on the
  run or by the capacity (`run_count`, `peers_bound`, `sound_satisfies`). The query theorems keep their statements;
  `encode` now takes the capacity and a prepared closure leaves room for
  questions that count 64 values. The other facets, facets on strings and data
  ranges of the other datatypes get no answer. `examples/medication-dose.ofn`
  checks paracetamol doses against daily maximums from its bytes.
- M5 data properties and literals in the ontology queries: consistency, class
  satisfiability, subsumption and instance checking (`data_ontology`) take data
  properties with their domains, ranges, inclusions, equivalences,
  disjointness and functionality, data restrictions (existential, universal,
  value and number restrictions) over the datatypes of
  `datatypes::literal_value` and their range restrictions (above),
  `rdfs:Literal`, literal enumerations and their intersections, unions and
  complements, and positive and negative data property assertions, with
  literals of every datatype of `datatypes::literal_value`. An encoding
  turns them into classes, object properties and named individuals that the
  SROIQ queries decide: the data values become data nodes of a class `D`, each
  data property an object property into them, each datatype in use a class
  with the inclusions and disjointness of the datatypes and the booleans as the
  two truth values, and each literal value a named data node that a pattern of
  bit classes keeps apart from the others. An OWL model lifts to a model of the
  encoding with its values as the data nodes, and a model of the encoding gives
  an OWL model in which each element takes its values from regions of numbers
  (see the numeric data ranges above), strings, tagged strings and values
  outside every datatype. Under every datatype map that is the OWL 2 map on the
  datatypes of `literal_value` an answer is therefore the Direct Semantics
  answer. Datatype restrictions other than the range facets on the numeric
  datatypes, datatype definitions, keys with a data property, data ranges of the
  other datatypes,
  `owl:topDataProperty` outside an inclusion into it and the universal role
  outside its own axioms get no answer, as does a question that names an
  individual the closure does not name. Since the source reasoning stage these
  answers also come straight from Functional Syntax bytes, which the reader
  reads with all their data axioms, data restrictions and data assertions.
- M5 keys with object properties in the ontology queries (`key_ontology`): a
  closure with `HasKey` axioms goes to `key_ontology::prepare`, which encodes
  the keys next to the data encoding of the other axioms. A fresh class `N` is
  asserted at every named individual of the closure, those of the keys' class
  expressions included, and kept apart from the data nodes. A key with one
  property `P`, in a closure without transitive properties and property
  chains, becomes `N ⊑ ≤1 P⁻.(CE ⊓ N)`; every other key gets a role `mark`
  whose self loops mark `N`, the chain `P ∘ mark ∘ P⁻ ⊑ share(P)` of each of its
  properties and, at every named individual `x`, the assertion
  `x : ∀share(P1).(¬N ⊔ ¬CE ⊔ {x} ⊔ ∀share(P2)⁻.¬{x} ⊔ … ⊔ ∀share(P1)⁻.(¬{x} ⊔ ¬CE))`.
  A model of the encoding gives an OWL model of the closure whose named
  elements are exactly the closure's named individuals
  (`keyed_encoded_model`), and an OWL model lifts to a model of the encoding
  with `N` its named elements (`keyed_lifted_model`), provided its vocabulary
  names the closure's individuals, since keys apply only to named individuals.
  So consistency, class satisfiability, subsumption, instance checking (about
  an individual the closure names) and classification are proved to give the
  Direct Semantics answer for every vocabulary that names the individuals of a
  closure with keys (`NamesKeyed`, which asks nothing of a closure without
  keys), also from source bytes, together with the numeric data ranges and
  range facets: the key encoding uses the data encoding with a capacity that
  counts the data restrictions of the keys' class expressions too. Keys apply
  neither to anonymous individuals nor through unnamed values. Keys with a data
  property, no property or the universal role get no answer.
- Classification of named classes: `classification::classify` answers, for a
  prepared closure and a list of named classes, whether each class is
  satisfiable and, for every pair, whether the first is subsumed by the second.
  It reads the told parents of every class from the subclass, equivalence and
  disjoint-union axioms that name it (`told`), orders the classes by their
  depth in that told hierarchy and fills each class's row along that order: a
  class is below itself, every class without instances is above no
  satisfiable class, a told parent is above, a class with a told parent the row
  already refuses is not above, and a class above a classified told parent is
  above. The pairs left open are tested in groups: one prepared satisfiability
  query asks whether the class has an instance outside every class of a group,
  which refutes the whole group when it has; otherwise the group is halved,
  and a single class the class cannot escape is a subsumer. Each round tests
  the open classes whose told parents all subsume the class, so their told
  children are refuted without a query, and a final test takes whatever is
  still open. A class without instances is below every class. Every told pair
  is proved subsumed in every model (`told_subsumed`), the group tests are
  proved to refute or confirm exactly (`escapes_spec`, `split_spec`), and
  `classify_correct` proves that whenever classification answers, each listed
  answer is exactly the Direct Semantics answer under every normative datatype
  map and vocabulary. `Reasoner::classify` and the CLI's `classify` command use
  it; on a generated 437-class ontology it runs 871 satisfiability queries
  where pairwise classification would ask about 190 000 questions.
- EL classification by saturation: `saturation::classify` classifies the
  named classes of an ontology whose logical axioms are EL: subclass,
  equivalent-class and disjoint-class axioms between class expressions built
  from named classes, `owl:Thing`, `owl:Nothing`, intersections and existential
  restrictions on named object properties; object property domains; inclusions
  and two-member equivalences of named object properties, chains of two of
  them and transitivity. Declarations and annotation axioms are ignored and any
  other axiom makes it decline. The class expressions are interned into a
  hashed table of concepts, and the axioms become rules over the table that
  hold exactly when the axioms do (`translate_spec`). Saturation derives the
  subsumers and links of every context from indexes of the told subsumers,
  conjunctions, existential restrictions, role inclusions and chains until no
  rule adds anything, and a final check confirms that the result is closed
  under every rule. Every derived subsumer and link is proved to hold in every
  model of the rules (`saturate_spec`), and an accepting check makes the
  closed state a canonical model of the axioms in which every context
  satisfies its subsumers and every registered concept that holds at a context
  is one of them (`closed_spec`, `positive`, `negative`, `canonical_models`).
  `classify_correct` proves every answer the Direct Semantics answer under
  every vocabulary and datatype map. `saturation::taxonomy` gives the same
  answers as lists of the subsuming classes, in space proportional to the
  subsumptions rather than the pairs (`taxonomy_correct`), and
  `saturation::consistent` decides consistency (`consistent_correct`).
  `Reasoner::classify` and `Reasoner::consistent` use them whenever the
  ontology is EL and the tableau otherwise, and the reasoner prepares the
  tableau queries only when a question needs them. A generated EL ontology with
  1000 classes classifies in 0.6 s instead of 19.5 s with the same answers, and
  one with 20 000 classes in under a second from N-Triples (2.2 s before the RDF
  mapping's lookups were indexed) and, since the proved name and IRI scanners
  of the lexer, about 1.2 s from Functional Syntax (12 s before).
- Python bindings: the `rowl` package in `bindings/python` reads a
  Functional Syntax, N-Triples, Turtle or RDF/XML document, or the import closure of one
  from a catalog of documents, once and answers consistency, satisfiability,
  subsumption, instance and classification questions by IRI. It calls the
  verified `Reasoner` through the C interface of the `rowl-python` crate with
  `ctypes`, needs no third-party Python or Rust packages, and installs with
  `pip install --no-build-isolation ./bindings/python`. The C interface and the
  Python layer are unverified glue that only converts text and adds no
  reasoning; the crate is the only one outside the kernel with `unsafe` code,
  confined to reading the caller's buffers and releasing handles.
- Reading OWL from RDF graphs: `rdf_mapping::map_graph` reads an ontology from
  a raw RDF graph by the reverse of the OWL 2 mapping to RDF graphs, for graphs
  that declare every class, datatype and property they use. Annotated axioms
  are read from the blank node typed `owl:Axiom` that reifies their main
  triple, or from the blank node that represents them, and annotations with
  annotations of their own from the blank node typed `owl:Annotation` that
  reifies them (§2.2, §2.3), in headers and axioms alike. `map_graph_correct` proves that
  whenever it returns an ontology and its blank nodes, the forward mapping of
  that ontology, stated independently in `RdfMapping.lean` and allocating
  exactly those blank nodes, gives the input graph: every triple instantiates
  one of its triple patterns and every pattern is instantiated by a triple.
  The forward mapping includes the annotations and their reifications. The
  converse is proved for every ontology without annotations that the reverse
  mapping reads back exactly: `RdfReadOntology.map_graph_complete` reads a graph
  that lists the forward mapping of the ontology in its order, with blank nodes
  distinct from each other and from the anonymous individuals its assertions are
  about, back to exactly that ontology, its version IRI and imports included,
  and those blank nodes. It covers ontologies that satisfy the reserved-vocabulary
  condition and the typing constraints of OWL 2 DL (every property declared or
  built in as one kind of property, no class a datatype), with unannotated
  axioms of every kind and class expressions and data ranges of every kind,
  except the forms the mapping writes as triples of other axioms: equivalences
  and equalities of three or more members, inverse-property axioms whose first
  member is an inverse, and object property assertions on an inverse. Literals
  must not be `rdf:PlainLiteral` with an empty language tag, cardinalities at
  most 10000 and facets those of OWL 2 (`ReadableOntology`). The EL theorem
  `RdfMappingComplete.map_graph_complete` stays, for EL ontologies without the
  vocabulary conditions. `RdfReadPermuted.map_graph_complete_perm` extends the
  theorem to graphs that list those triples in any order: they are read back to
  the same ontology with its axioms and imports up to their order, and to the
  same blank nodes up to their order; the reader needed no change.
  `RdfReadAnnotated.map_graph_complete_annotated` adds annotations: a graph that
  lists the forward mapping of an ontology with ontology annotations and
  annotated axioms in order is read back to exactly that ontology, its
  annotations and those of its axioms in order included, when the annotations
  have no annotations of their own and every annotated axiom has one main
  triple, reified by a node typed `owl:Axiom`, and occurs in the ontology once
  (`ReadableAnnotated`).
  `RdfReadAnnotatedPermuted.map_graph_complete_annotated_perm` extends it to
  graphs that list those triples in any order: they are read back to the same
  ontology with its imports, annotations and axioms up to their order, each
  axiom with its annotations up to their order, and to the same blank nodes up
  to their order; again the reader needed no change. Annotations of
  annotations, annotated axioms that a blank node represents, repeated triples,
  several reifications of one main triple and distinct blank nodes are not
  proved; import closures are assembled from the documents separately
  (`import_closure`).
  `Reasoner::from_ntriples` and `Reasoner::from_turtle`, the CLI's `check`,
  `classify`, `instances` and `validate` commands for `.nt` and `.ttl` files and
  the Python package read N-Triples and Turtle documents through the verified
  readers and this mapping. Its
  lookups of the triples about a blank node and of declarations go through
  buckets by hash, built once, and check every candidate, so the proofs hold
  whatever the buckets contain; a generated 20 000-class ontology now maps in
  0.06 s instead of 2.5 s.
- 5453 audited public theorems and 1818 audited semantic definitions. Consistency,
  class satisfiability, subsumption, instance checking and the classification
  of named classes are decided, with
  proofs against the OWL definitions, for axiom closures whose logical axioms are
  ALCIQO class, domain and range axioms with number restrictions on simple
  roles, nominals of named individuals and self restrictions, functional,
  inverse functional, reflexive, irreflexive, asymmetric and disjoint object
  properties, class, object property and negative object property
  assertions, individual equalities and inequalities, and inclusions,
  equivalences, inverses, symmetry, transitivity and chains of object property
  expressions, with the universal and empty roles (SROIQ), also directly from
  Functional Syntax source bytes, and with data properties, data restrictions
  over nineteen datatypes, with the range facets on the numeric ones, and data
  assertions with their literals under the OWL 2 datatype map, and keys with
  object properties;
  EL ontologies are also classified and checked for consistency by a proved
  saturation procedure.
  No full OWL decision procedure is proved yet. See m3-m4-progress.md for the
  input contracts.
- 666 Rust regression tests and 24 Python binding tests, plus separately fetched
  W3C corpora (68 N-Triples syntax cases, 313 Turtle cases and 166 RDF/XML
  cases, `scripts/fetch-*-suite.py`);
  maintenance OWL/RDF examples, a medication-safety example answered from its
  bytes, and CLI status/demo/check-nt/export-nt/validate commands. The SHI queries use
  lazy unfolding with absorption (unfoldings indexed by their triggering
  entry), a concept table prepared once per ontology, clash detection on
  insertion, anywhere equality blocking and backjumping, the queries that count or have nominals a
  completion forest with pairwise blocking and backjumping over merges; both
  pass restrictions along edges before giving nodes the TBox concept, so a
  choice that clashes with a neighbour fails before other nodes branch; an
  instance question about an individual of a consistent closure whose other
  axioms name no individual asks only the part with the individual's component
  of assertions (`components::closure_parts` finds all components once, proved
  to give the same answer by `Rowl.Components.parts_instance_correct`), and its satisfiability,
  subsumption and classification questions ask only the axioms other than
  assertions (`components::tbox_closure`, `part_satisfiable_correct`,
  `part_subsumed_correct`); such a closure's consistency is decided part by
  part, from its axioms other than assertions and the part of each component
  (`components::consistent_by_parts`, `consistent_by_parts_correct`); and a
  closure or document prepared once answers any number of queries. A closure
  entails a property assertion about named individuals, its negative, or an
  equality or inequality of two named individuals exactly when it has no model
  together with the fact's negation (`Rowl.Facts.entails_iff_inconsistent`);
  `facts::entails_fact` decides it so (`entails_fact_correct`), and the
  Reasoner, the CLI command `entails` and the Python bindings ask it.
- Exact-source linkage covering Rust, proof sources and audit/inventory gates.
  The frontend stages are extracted together with the kernel as one Lean
  development, so parsing and reasoning can be composed without assumptions;
  `rowl-frontend` re-exports them.
  Extraction rejects unknown external axioms/opaque declarations. Every public
  project theorem is audited; allowed logical axioms remain only propext,
  Classical.choice and Quot.sound.
- A 5646-obligation release ledger and separate checked constructor and built-in inventories.
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
checked laws. The UTF-8/XML character component is proved from bytes. Catalog and
import metadata are derived from Functional Syntax, N-Triples and Turtle bytes by
the verified readers, and the import closure is assembled from them with its
meaning proved (`import_catalog`, `import_closure`); RDF documents are read without
the declarations of the documents they import. The
symbol table and raw-ontology checker operate directly on byte-buffer IRIs,
without an unproved String conversion, but do not invoke lexical validation; a separate IRI byte entry point is now
proved sound/complete against RFC 3987. The UTF-8 encoder and complete language-tag recognizer are also proved.
The N-Triples token subpipeline now includes composed byte-to-blank-token
correctness and complete acceptance, exact trivia/span-copy proofs and full
quoted-token, IRIREF, language/literal/object/triple and bounded whole-document
composition. Public reading is proved from bytes to exact raw graph occurrences
under its stated term/count limits. The RDF-to-OWL mapping is proved sound,
annotated axioms included, and complete for every ontology without annotations
that it reads back exactly, and for ontology annotations and annotated axioms
with one main triple, its triples in any order; the writer, the termination
of the mapping, the completeness of that mapping for annotations of
annotations and for annotated axioms that a blank node represents remain unproved; so the
byte-to-ontology pipeline from RDF (`import_catalog::read_source`) is proved
correct whenever it returns (`read_source_correct`) but not proved to return. Correspondence to W3C prose/tables is
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
entity declarations, annotation axioms, all class expressions and data ranges,
all logical axioms and whole documents with their closing syntax and end of
source. Read
documents map into the raw model with a proved exact correspondence, and the ALC
queries compose with the reader and the mapping from the original bytes; the
catalog and the import closure are assembled from the bytes of the documents
(`import_catalog`, `import_closure`).

Datatype maps are explicit parameters with their stated laws, not an assumed
external solver. Agreement with the OWL 2 map on nineteen datatypes and the
four range facets is specified (Rowl.DatatypeMap.Normative) and satisfiable,
and the data queries, range facets included, are proved under every such map;
the complete normative OWL map, its other datatypes and facets are
unimplemented. Semantic
predicates extend to raw terms; release callers must first establish lexical
validity and canonical structure; `import_closure` assembles the complete import
closure. The structural,
vocabulary, typing and global DL restrictions are decided by the verified
`dl_validity::check_ontology` on the supplied axioms.
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
2. M4: the structural and global DL restrictions are composed into one verified
   check (`dl_validity`); normalization and role preprocessing for reasoning
   remain, and lexical and facet validity wait for the M5 datatype map.
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
