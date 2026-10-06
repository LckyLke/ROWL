<img src="assets/rusty-owl.svg" alt="ROWL logo: a rusty owl" width="140" align="right">

# ROWL: Rust OWL

**An OWL 2 reasoner in Rust whose answers come with a machine-checked proof,
from the bytes of the ontology file to the final yes or no.**

> Research project, work in progress. The proofs cover a growing part of OWL
> today (see [Status](#status)); full OWL 2 DL is the goal, not yet the present.

## Why

Ontologies written in [OWL](https://www.w3.org/TR/owl2-overview/) record what a
field knows: diseases and drugs, genes, the parts of a machine. A *reasoner*
draws the conclusions: it finds contradictions, builds class hierarchies and
answers questions such as *"does this prescription conflict with the patient's
allergies?"*

Reasoners are large, heavily optimised programs. When one is wrong, the wrong
answer looks exactly like a right one; all that stands behind it is trust in the
code. That is a weak foundation for conclusions that feed medicine, safety
reviews or further automated decisions.

ROWL takes the other route: **don't trust the code, check it.**

| | Typical reasoner | ROWL |
| --- | --- | --- |
| Why believe an answer? | The code was tested | A theorem about the code was machine-checked |
| What you have to trust | The whole optimised reasoner | Lean's small proof kernel, the Rust compiler and translation tools, and the written-down semantics |

## How

The reasoner is ordinary Rust. Charon and Aeneas translate that exact code into
the proof assistant [Lean 4](https://lean-lang.org). There it is proved correct
against a formalisation of the W3C OWL 2 Direct Semantics that is written
independently of the code.

```mermaid
flowchart TB
    subgraph runs ["What runs"]
        direction LR
        F["📄 ontology file"] -->|bytes| P["parser"] --> R["reasoner"] --> A["✅ answer"]
    end
    runs -->|"Charon + Aeneas translate<br/>the exact Rust code"| L["the same functions,<br/>now in Lean 4"]
    W["W3C OWL 2<br/>Direct Semantics,<br/>written independently<br/>in Lean 4"] --> T
    L --> T{{"machine-checked theorem:<br/>it always terminates, and<br/>its answer is exactly<br/>what the semantics says"}}
    style T fill:#dff5e1,stroke:#2e7d32,color:#000
```

Concretely, the theorems say:

- **It terminates.** Every verified function is proved to terminate on every
  input.
- **The parser is exact.** A document is accepted exactly when an independent
  grammar derives it, and errors report the first failing position.
- **The answers are exact.** Each yes or no equals the W3C definition of
  consistency, satisfiability, subsumption or instance checking, over all
  models, however large. Outside the supported fragment there is no answer
  rather than a wrong one.
- **No shortcuts.** No `sorry`, no admitted lemmas, no custom axioms: all 1100+
  public theorems are audited to depend only on Lean's three standard axioms.

## Example

[`examples/medication-safety.ofn`](examples/medication-safety.ofn) records, in
OWL Functional Syntax (abridged):

```text
TransitiveObjectProperty(ex:contains)
SubObjectPropertyOf(ex:hasActiveIngredient ex:contains)
SubClassOf(ex:Amoxicillin ex:Penicillin)
SubClassOf(ex:Azithromycin ex:Macrolide)
DisjointClasses(ex:Penicillin ex:Macrolide)
SubClassOf(ObjectIntersectionOf(ObjectSomeValuesFrom(ex:hasAllergy ex:PenicillinAllergy)
                                ObjectSomeValuesFrom(ex:receives
                                  ObjectSomeValuesFrom(ex:contains ex:Penicillin)))
           ex:AllergyAlert)
ClassAssertion(ObjectSomeValuesFrom(ex:hasAllergy ex:PenicillinAllergy) ex:alice)
ObjectPropertyAssertion(ex:receives ex:alice ex:comboPack)
ObjectPropertyAssertion(ex:receives ex:bob ex:comboPack)
ObjectPropertyAssertion(ex:contains ex:comboPack ex:capsule)
ClassAssertion(ObjectSomeValuesFrom(ex:hasActiveIngredient ex:Amoxicillin) ex:capsule)
ClassAssertion(ObjectSomeValuesFrom(ex:hasAllergy ex:PenicillinAllergy) ex:carol)
ObjectPropertyAssertion(ex:receives ex:carol ex:tablet)
ClassAssertion(ObjectSomeValuesFrom(ex:hasActiveIngredient ex:Azithromycin) ex:tablet)
```

```console
$ cargo run -p rowl --example medication_safety
The records are consistent: true
alice needs an allergy alert: true
bob needs an allergy alert: false
carol needs an allergy alert: false
carol's tablet has an active ingredient that is no penicillin: true
```

alice is allergic to penicillins. Her combination pack contains a capsule
whose active ingredient is amoxicillin, which is a penicillin. The penicillin
is two levels down, where a check that looks only at the pack would miss it.
Because `contains` is transitive and every active ingredient is contained, the
alert follows in every model of the records. bob receives the same pack, but no
allergy is recorded. carol has the same allergy, but her tablet's active
ingredient is azithromycin, a macrolide, and macrolides are disjoint from
penicillins, so the records prove that this ingredient is no penicillin. For bob
and carol the alert does not follow. "false" means *not entailed by the
records*, not *proved safe*. Each answer comes from code proved to compute
exactly the Direct Semantics of the bytes in that file. (An illustration, not
clinical guidance.)

## Status

The Rust model represents every OWL 2 DL construct, and the Lean semantics gives
every one of them its meaning. The verified reasoner covers a growing fragment:

| | ✅ Proved today | 🔜 Next |
| --- | --- | --- |
| **Input** | OWL Functional Syntax documents: prefixes, header, annotations and every one of the 37 axiom forms, with all 18 class expressions and all data ranges; N-Triples, passing all 68 W3C syntax tests, and the OWL ontologies N-Triples graphs encode, read by the reverse OWL RDF mapping, proved to read back exactly the graph of the ontology it returns for axioms without annotations | imports, RDF/XML, Turtle and the other required formats |
| **Logic** | ALC (and, or, not, some, only) with named individuals, equal and different individuals, inverse roles, role hierarchies, transitive roles, number restrictions, including functional properties, nominals of named individuals, such as enumerations and value restrictions (SHOIQ), self restrictions, reflexive, irreflexive, asymmetric and disjoint properties, role chains and the universal and empty roles (SROIQ); data properties, data restrictions and literals of `xsd:integer`, `xsd:decimal`, `xsd:string`, `rdf:PlainLiteral` and `xsd:boolean` | datatype facets, the other datatypes and keys, up to full OWL 2 DL (SROIQ(D)) |
| **Questions** | consistency, class satisfiability, subsumption, instance checking, classification of the named classes | query answering |
| **Validation** | whether a document is OWL 2 DL: keys and arities, the reserved vocabulary, declarations and typing, and the global restrictions on simple roles, property hierarchies, datatypes and anonymous individuals, with the first violation in words (`rowl validate FILE`, `Reasoner.dl_violation()`) | the lexical forms of literals, facet values and imports |
| **Scale** | a completion graph tableau with lazy unfolding, absorption, early clash detection, anywhere equality blocking and backjumping, and a completion forest with pairwise blocking for counting, nominals and self restrictions; a document read once, with its queries prepared once when first needed, answers any number of queries; classification settles what told subclass axioms and earlier answers decide and tests the rest in groups, and classifies EL ontologies by saturation in one pass | model-based pruning and incremental rule search |

There is no release yet: v0.1 requires all of OWL 2 DL, the normative datatypes
and proofs from bytes to answers. [`docs/status.md`](docs/status.md) states
exactly what is proved and what is not.

## Quick start

```sh
python3 scripts/bootstrap.py        # hash-pinned Rust, Lean and Aeneas (Linux x86_64, Python 3.12+)
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cargo test --workspace              # regression tests
cargo run -p rowl --example medication_safety
python3 scripts/verify.py           # re-translate the Rust code and re-check every proof
```

[`crates/rowl/examples`](crates/rowl/examples) has one runnable example per
stage, from IRI checks to the `tbox`, `alc_ontology` and `shi_ontology` reasoners.

## Python

```sh
pip install --no-build-isolation ./bindings/python   # builds the Rust library with cargo
```

```python
import rowl

with rowl.Reasoner.from_file("examples/medication-safety.ofn") as r:
    med = "https://example.org/medication/"
    r.instance_of(med + "alice", med + "AllergyAlert")      # True
    r.subsumed(med + "Amoxicillin", med + "Penicillin")    # True
    r.classify()                                            # every class with its superclasses
```

Answers are `True`, `False` (not entailed) or `None` (outside the supported
fragment). The bindings pass text to the verified Rust functions through a
small C interface and add no reasoning; see
[`bindings/python`](bindings/python/README.md).

## Repository

| Path | Contents |
| --- | --- |
| `crates/rowl-kernel` | The verified code, parser and reasoner, translated to Lean as one unit |
| `verification/` | The generated Lean translation, the OWL 2 semantics, the proofs and the theorem registry |
| `crates/rowl`, `crates/rowl-cli` | Examples and a thin command-line tool |
| `crates/rowl-python`, `bindings/python` | The C interface and the Python package over it |
| [`docs/status.md`](docs/status.md) | The precise proof boundary |
| [`docs/architecture.md`](docs/architecture.md) | Design decisions, semantic pitfalls, milestones and release gates |
| [`docs/m3-m4-progress.md`](docs/m3-m4-progress.md) | Each verified stage and its input contract |

## Fine print

- "Proved" means the answer follows from the ontology as written. Whether its
  statements are true in the world is a different question.
- Answers assume enough time and memory. Typed outcomes for exhausted resources
  and cancellation are planned work.

Intended license: MIT OR Apache-2.0.
