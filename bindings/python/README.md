# rowl for Python

Python bindings for ROWL, an OWL 2 reasoner written in Rust whose reader,
mapping and queries are proved in Lean against the OWL 2 Direct Semantics.
A `Reasoner` reads an OWL Functional Syntax or N-Triples document once and
answers any number of questions about it by IRI. An N-Triples graph is read as
the OWL ontology it encodes by the verified reverse OWL RDF mapping.

```python
import rowl

with rowl.Reasoner.from_file("examples/medication-safety.ofn") as r:
    med = "https://example.org/medication/"
    r.consistent()                                          # True
    r.subsumed(med + "Amoxicillin", med + "Penicillin")    # True
    r.instance_of(med + "alice", med + "AllergyAlert")      # True
    r.instance_of(med + "bob", med + "AllergyAlert")        # False: not entailed
    for entry in r.classify():
        print(entry.iri, entry.satisfiable, entry.superclasses)
```

`Reasoner.from_file` reads N-Triples for a `.nt` file and Functional Syntax
otherwise; `Reasoner(text, syntax="ntriples")` reads N-Triples text.

Every answer is `True`, `False` or `None`. `None` means the question is
outside the supported fragment (see the repository's `docs/status.md`) or a
limit was reached. `False` means *not entailed by the axioms*, not *proved
false*. Loading raises `rowl.DocumentRejected` when the verified reader
rejects the document or its RDF graph is not the mapping of an OWL ontology
the verified reverse mapping reads, and `rowl.UnsupportedOntology` when the
read document does not map into the OWL model.

| Method | Question |
| --- | --- |
| `consistent()` | Do the axioms have a model? |
| `satisfiable(cls)` | Does some model have an instance of the named class? |
| `subsumed(sub, sup)` | Is every instance of `sub` an instance of `sup` in every model? |
| `instance_of(individual, cls)` | Is the named individual an instance of the named class in every model? |
| `classes()`, `individuals()` | The named classes and individuals of the document |
| `classify()` | Every named class with its named superclasses |
| `superclasses(cls)` | The named superclasses of one named class |

## Installing

The package builds the native library with cargo, so it needs the Rust
toolchain of the repository (`python3 scripts/bootstrap.py`). From the
repository root:

```sh
pip install --no-build-isolation ./bindings/python
```

`--no-build-isolation` uses the installed setuptools instead of downloading
one. In a source checkout the package also works without installing: build
the library with `cargo build --release -p rowl-python`, and `import rowl`
from `bindings/python` finds it in `target/release` (or set `ROWL_LIBRARY` to
the library's path).

## What is verified

The answers come from the verified Rust functions; the bindings themselves are
an unverified layer that passes text across the C interface of the
`rowl-python` crate and decodes the JSON it returns. Tests:
`python3 -m unittest discover -s bindings/python/tests -t bindings/python` after building the
library, and `cargo test -p rowl-python` for the C interface.
