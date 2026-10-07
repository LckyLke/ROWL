# rowl for Python

Python bindings for ROWL, an OWL 2 reasoner written in Rust whose reader,
mapping and queries are proved in Lean against the OWL 2 Direct Semantics.
A `Reasoner` reads an OWL Functional Syntax, N-Triples or Turtle document
once and answers any number of questions about it by IRI. An N-Triples or
Turtle graph is read as the OWL ontology it encodes by the verified reverse OWL
RDF mapping.

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
    r.dl_violation()                                        # None: the document is OWL 2 DL
```

`Reasoner.from_file` reads N-Triples for a `.nt` file, Turtle for a `.ttl`
file and Functional Syntax otherwise; `Reasoner(text, syntax="ntriples")` and
`Reasoner(text, syntax="turtle")` read N-Triples and Turtle text. A relative IRI
in Turtle needs an `@base` or `BASE` directive before it.

Every answer is `True`, `False` or `None`. `None` means the question is
outside the supported fragment (see the repository's `docs/status.md`) or a
limit was reached. `False` means *not entailed by the axioms*, not *proved
false*. Loading raises `rowl.DocumentRejected` when the verified reader
rejects the document or its RDF graph is not the mapping of an OWL ontology
the verified reverse mapping reads, `rowl.UnsupportedOntology` when the
read document does not map into the OWL model, and `rowl.ImportUnresolved`
when an import of an import closure names no document of the catalog, or
several.

| Method | Question |
| --- | --- |
| `consistent()` | Do the axioms have a model? |
| `satisfiable(cls)` | Does some model have an instance of the named class? |
| `subsumed(sub, sup)` | Is every instance of `sub` an instance of `sup` in every model? |
| `instance_of(individual, cls)` | Is the named individual an instance of the named class in every model? |
| `classes()`, `individuals()` | The named classes and individuals of the document |
| `classify()` | Every named class with its named superclasses |
| `superclasses(cls)` | The named superclasses of one named class |
| `dl_violation()` | The first OWL 2 DL restriction the document violates, or `None` |

`dl_violation()` reports the verdict of the verified OWL 2 DL check: keys and
arities, the reserved vocabulary, declarations and typing, and the global
restrictions of the OWL 2 Structural Specification, proved exact against their
conjunction. It is computed when called; loading never rejects a document for
these restrictions. For an import closure it checks the axioms of all its
documents, so imported declarations count. The lexical forms of literals and
facet values are not checked yet.

## Import closures

An ontology that imports others is read together with them from a catalog of
documents; nothing is fetched:

```python
with rowl.Reasoner.from_file("examples/imports/medication-prescriptions.ofn",
                             imports=["examples/imports"]) as r:
    r.instance_of(med + "alice", med + "AllergyAlert")      # True
    r.dl_violation()                                        # None: imported declarations count
```

`imports` lists further files of the catalog; a directory contributes its
`.ofn`, `.nt` and `.ttl` files. `Reasoner.from_documents([(name, text, syntax),
...], root=0)` takes the catalog as text, `syntax` being `"functional"`,
`"ntriples"` or `"turtle"` (Turtle without a base IRI). Every import IRI of a
document of the import closure must be the ontology IRI or version IRI of
exactly one document of the catalog; otherwise loading raises
`rowl.ImportUnresolved`, naming the document and the IRI. The verified assembly
keeps every document's anonymous individuals apart, and the answers are proved
to be those of the whole import closure. RDF documents are read without the
declarations of the documents they import, so an N-Triples or Turtle document
must declare what it uses.

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
