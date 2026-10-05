"""Python bindings for ROWL, an OWL 2 reasoner with proved answers.

A :class:`Reasoner` reads an OWL Functional Syntax or N-Triples document once
and answers any number of questions about it by IRI. Every answer comes from the
verified Rust pipeline (the document reader, the mapping into the OWL model —
for N-Triples the reverse OWL RDF mapping — and the prepared queries), which is
proved against the OWL 2 Direct Semantics; this package only passes text across
the C interface of the ``rowl-python`` crate.

An answer is ``True`` or ``False``, or ``None`` when the question is outside
the supported fragment or a limit was reached. ``False`` means *not entailed*,
not *proved false*.
"""
from __future__ import annotations

import ctypes
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Union

__all__ = [
    "Classified",
    "DocumentRejected",
    "Reasoner",
    "RowlError",
    "UnsupportedOntology",
    "library_version",
]


class RowlError(Exception):
    """A document could not be loaded."""


class DocumentRejected(RowlError):
    """The verified reader rejected the document, or its RDF graph is not the
    mapping of an OWL ontology that the verified reverse mapping reads."""


class UnsupportedOntology(RowlError):
    """The document's axioms are outside the reasoner's supported fragment."""


@dataclass(frozen=True)
class Classified:
    """One named class of a classification."""

    iri: str
    satisfiable: bool
    superclasses: List[str]


def _library_name() -> str:
    if sys.platform == "darwin":
        return "librowl_python.dylib"
    if sys.platform == "win32":
        return "rowl_python.dll"
    return "librowl_python.so"


def _candidates() -> List[Path]:
    found = []
    configured = os.environ.get("ROWL_LIBRARY")
    if configured:
        found.append(Path(configured))
    here = Path(__file__).resolve().parent
    found.append(here / _library_name())
    # A source checkout: bindings/python/rowl next to the cargo target directory.
    root = here.parents[2]
    target = Path(os.environ.get("CARGO_TARGET_DIR", root / "target"))
    for profile in ("release", "debug"):
        found.append(target / profile / _library_name())
    return found


def _load() -> ctypes.CDLL:
    for path in _candidates():
        if path.is_file():
            return ctypes.CDLL(str(path))
    raise ImportError(
        "the ROWL library was not found; build it with "
        "`cargo build --release -p rowl-python` or set ROWL_LIBRARY"
    )


_lib = _load()
_text = ctypes.c_char_p
_size = ctypes.c_size_t
_handle = ctypes.c_void_p

_lib.rowl_version.argtypes = []
_lib.rowl_version.restype = ctypes.c_char_p
_lib.rowl_reasoner_from_functional.argtypes = [_text, _size, ctypes.POINTER(ctypes.c_int32)]
_lib.rowl_reasoner_from_functional.restype = _handle
_lib.rowl_reasoner_from_ntriples.argtypes = [_text, _size, ctypes.POINTER(ctypes.c_int32)]
_lib.rowl_reasoner_from_ntriples.restype = _handle
_lib.rowl_reasoner_free.argtypes = [_handle]
_lib.rowl_reasoner_free.restype = None
_lib.rowl_consistent.argtypes = [_handle]
_lib.rowl_consistent.restype = ctypes.c_int32
_lib.rowl_satisfiable.argtypes = [_handle, _text, _size]
_lib.rowl_satisfiable.restype = ctypes.c_int32
_lib.rowl_subsumed.argtypes = [_handle, _text, _size, _text, _size]
_lib.rowl_subsumed.restype = ctypes.c_int32
_lib.rowl_instance_of.argtypes = [_handle, _text, _size, _text, _size]
_lib.rowl_instance_of.restype = ctypes.c_int32
for _name in ("rowl_classes", "rowl_individuals", "rowl_classify"):
    getattr(_lib, _name).argtypes = [_handle]
    getattr(_lib, _name).restype = ctypes.c_void_p
_lib.rowl_string_free.argtypes = [ctypes.c_void_p]
_lib.rowl_string_free.restype = None

_LOADED, _REJECTED, _UNSUPPORTED, _UNMAPPED = 0, 1, 2, 4


def library_version() -> str:
    """The version of the loaded ROWL library."""
    return _lib.rowl_version().decode("utf-8")


def _answer(code: int) -> Optional[bool]:
    if code == 1:
        return True
    if code == 0:
        return False
    if code == -1:
        return None
    raise ValueError("invalid argument")


def _utf8(text: str) -> bytes:
    if not isinstance(text, str):
        raise TypeError("expected an IRI as str")
    return text.encode("utf-8")


class Reasoner:
    """An OWL Functional Syntax or N-Triples document read and prepared once.

    ``syntax`` is ``"functional"`` (the default) or ``"ntriples"``; an
    N-Triples graph is read as the OWL ontology it encodes by the verified
    reverse RDF mapping.

    >>> r = Reasoner.from_file("examples/medication-safety.ofn")  # doctest: +SKIP
    >>> r.subsumed("https://example.org/medication/Amoxicillin",
    ...            "https://example.org/medication/Penicillin")  # doctest: +SKIP
    True
    """

    def __init__(self, source: Union[str, bytes], syntax: str = "functional"):
        data = source.encode("utf-8") if isinstance(source, str) else bytes(source)
        status = ctypes.c_int32(-1)
        if syntax == "functional":
            handle = _lib.rowl_reasoner_from_functional(data, len(data), ctypes.byref(status))
            rejected = "not a Functional Syntax document the verified reader accepts"
        elif syntax == "ntriples":
            handle = _lib.rowl_reasoner_from_ntriples(data, len(data), ctypes.byref(status))
            rejected = "not an N-Triples document the verified reader accepts"
        else:
            raise ValueError("syntax must be 'functional' or 'ntriples'")
        if not handle:
            if status.value == _REJECTED:
                raise DocumentRejected(rejected)
            if status.value == _UNMAPPED:
                raise DocumentRejected(
                    "the graph is not the RDF mapping of an OWL ontology the verified mapping reads")
            if status.value == _UNSUPPORTED:
                raise UnsupportedOntology("the axioms are outside the reasoner's supported fragment")
            raise RowlError("the document could not be loaded")
        self._handle = handle

    @classmethod
    def from_file(cls, path: Union[str, os.PathLike], syntax: Optional[str] = None) -> "Reasoner":
        """Read a document from a file: N-Triples for a ``.nt`` file and
        Functional Syntax otherwise, unless ``syntax`` says which."""
        path = Path(path)
        if syntax is None:
            syntax = "ntriples" if path.suffix == ".nt" else "functional"
        return cls(path.read_bytes(), syntax)

    def close(self) -> None:
        """Release the prepared document; further questions raise ``ValueError``."""
        handle, self._handle = getattr(self, "_handle", None), None
        if handle:
            _lib.rowl_reasoner_free(handle)

    def __enter__(self) -> "Reasoner":
        return self

    def __exit__(self, *exception) -> None:
        self.close()

    def __del__(self) -> None:
        self.close()

    def _live(self) -> int:
        if not self._handle:
            raise ValueError("the reasoner is closed")
        return self._handle

    def _json(self, function) -> object:
        pointer = function(self._live())
        if not pointer:
            raise RowlError("the library returned no text")
        try:
            return json.loads(ctypes.string_at(pointer).decode("utf-8"))
        finally:
            _lib.rowl_string_free(pointer)

    def consistent(self) -> Optional[bool]:
        """Whether the axioms have a model."""
        return _answer(_lib.rowl_consistent(self._live()))

    def satisfiable(self, cls: str) -> Optional[bool]:
        """Whether some model has an instance of the named class."""
        iri = _utf8(cls)
        return _answer(_lib.rowl_satisfiable(self._live(), iri, len(iri)))

    def subsumed(self, sub: str, sup: str) -> Optional[bool]:
        """Whether every instance of ``sub`` is an instance of ``sup`` in every model."""
        left, right = _utf8(sub), _utf8(sup)
        return _answer(_lib.rowl_subsumed(self._live(), left, len(left), right, len(right)))

    def instance_of(self, individual: str, cls: str) -> Optional[bool]:
        """Whether the named individual is an instance of the named class in every model."""
        who, what = _utf8(individual), _utf8(cls)
        return _answer(_lib.rowl_instance_of(self._live(), who, len(who), what, len(what)))

    def classes(self) -> List[str]:
        """The named classes the document declares or uses, sorted by IRI."""
        return list(self._json(_lib.rowl_classes))

    def individuals(self) -> List[str]:
        """The named individuals the document asserts something about, sorted by IRI."""
        return list(self._json(_lib.rowl_individuals))

    def classify(self) -> Optional[List[Classified]]:
        """Every named class with its named superclasses (itself excluded), or
        ``None`` if some question has no answer. An unsatisfiable class lists no
        superclasses."""
        entries = self._json(_lib.rowl_classify)
        if entries is None:
            return None
        return [
            Classified(entry["class"], entry["satisfiable"], list(entry["superclasses"]))
            for entry in entries
        ]

    def superclasses(self, cls: str) -> Optional[List[str]]:
        """The named superclasses of a named class, from the classification."""
        classified = self.classify()
        if classified is None:
            return None
        for entry in classified:
            if entry.iri == cls:
                return entry.superclasses
        return []
