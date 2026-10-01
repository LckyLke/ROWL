#!/usr/bin/env python3
"""Re-extract actual Rust, check exact-source linkage, and check Lean proofs.

This script verifies only the entry points and specification in toolchain.json.
It cannot make the full OWL coverage ledger release-ready.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
VERIFICATION = ROOT / "verification"
PINS = json.loads((VERIFICATION / "toolchain.json").read_text())
REGISTRY = json.loads((VERIFICATION / "theorems.json").read_text())
THEOREMS = [name for module in REGISTRY["modules"] for name in module["theorems"]]
AUDITED = THEOREMS + REGISTRY["specifications"]


def run(arguments, environment, cwd=ROOT, capture=False):
    print("+ " + " ".join(map(str, arguments)), flush=True)
    result = subprocess.run(list(map(str, arguments)), cwd=cwd, env=environment,
                            text=True, capture_output=capture)
    if capture:
        print(result.stdout, end="", flush=True)
        if result.returncode:
            print(result.stderr, end="", flush=True)
    result.check_returncode()
    if capture:
        return result.stdout
    return ""


def digest(path):
    with path.open("rb") as contents:
        return hashlib.file_digest(contents, "sha256").hexdigest()


def linkage():
    paths = [ROOT / "Cargo.toml", ROOT / "Cargo.lock", ROOT / "rust-toolchain.toml",
             ROOT / "crates/rowl-kernel/Cargo.toml", VERIFICATION / "toolchain.json"]
    for extraction in PINS["extractions"]:
        crate = ROOT / "crates" / extraction["crate"]
        paths.append(crate / "Cargo.toml")
        paths.extend(sorted((crate / "src").rglob("*.rs")))
    paths.extend(sorted(path for path in (VERIFICATION / "Rowl").rglob("*.lean")
                        if "Generated" not in path.parts))
    paths.extend([VERIFICATION / "Rowl.lean", VERIFICATION / "theorems.json",
                  ROOT / "docs/model-inventory.json", ROOT / "docs/coverage.json",
                  ROOT / "docs/builtin-vocabulary.json",
                  ROOT / "docs/functional-terminals.json",
                  ROOT / "scripts/verify.py"])
    return {str(path.relative_to(ROOT)): digest(path) for path in paths}


def check_dependency_pins():
    manifest = json.loads((VERIFICATION / "lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    if mathlib["rev"] != PINS["aeneas"]["mathlib_commit"]:
        raise RuntimeError("Lean dependency manifest does not match the pinned mathlib commit")
    for package in manifest["packages"]:
        if package["type"] == "git":
            checkout = VERIFICATION / ".lake/packages" / package["name"]
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
            if actual != package["rev"]:
                raise RuntimeError(f"Wrong dependency revision: {package['name']}")


def mathlib_cache_roots():
    # The cache reader does not follow Aeneas' new `public import` declarations.
    # Request the directly imported Mathlib modules explicitly. This is only a
    # build-speed aid: `lake build` still checks all required local proof code.
    modules = set()
    pattern = r"(?m)^(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+(Mathlib\.[A-Za-z0-9_.]+)"
    sources = list((ROOT / ".tools/aeneas/backends/lean").rglob("*.lean"))
    sources.extend((VERIFICATION / "Rowl").rglob("*.lean"))
    for source in sources:
        if ".lake" not in source.parts:
            modules.update(re.findall(pattern, source.read_text()))
    if not modules:
        raise RuntimeError("Could not locate pinned Mathlib imports for cache setup")
    return sorted(modules)


def check_inventory():
    inventory = json.loads((ROOT / "docs/coverage.json").read_text())
    identifiers = set()
    for entry in inventory["requirements"]:
        if entry["id"] in identifiers or not entry["owner"] or not entry["source"]:
            raise RuntimeError(f"Invalid coverage entry: {entry['id']}")
        identifiers.add(entry["id"])
        if entry["status"] not in {"planned", "implemented", "verified"}:
            raise RuntimeError(f"Unknown coverage status: {entry['id']}")
        if entry["status"] == "verified":
            if not all(entry[field] for field in ["rust_symbol", "theorem", "regression"]):
                raise RuntimeError(f"Unsubstantiated proof coverage: {entry['id']}")
            if entry["theorem"] not in THEOREMS:
                raise RuntimeError(f"Theorem is outside the audited scope: {entry['id']}")
    # The prototype cannot establish the full language, regardless of proof success.
    if inventory["release_ready"]:
        raise RuntimeError("Full OWL release is not implemented; release_ready must stay false")
    print(f"Coverage inventory valid: {len(identifiers)} obligations; full release pending.", flush=True)


def check_axioms(output):
    for theorem in AUDITED:
        pattern = re.escape(theorem) + r"[^\n]*?(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        match = re.search(pattern, output)
        if not match:
            raise RuntimeError(f"Missing kernel axiom audit: {theorem}")
        axioms = {value.strip() for value in (match.group(1) or "").split(",") if value.strip()}
        unexpected = axioms - set(PINS["allowed_theorem_axioms"])
        if unexpected:
            raise RuntimeError(f"Unapproved theorem assumptions for {theorem}: {unexpected}")


def check_generated(source):
    # Aeneas can emit opaque external-function axioms without an extraction
    # failure. Reject these even when no currently audited theorem uses them.
    if re.search(r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|opaque)\s", source):
        raise RuntimeError("Unsupported/opaque Rust translation introduced an unproved declaration")


def check_proof_sources():
    if len(AUDITED) != len(set(AUDITED)):
        raise RuntimeError("Duplicate axiom-audit entry")
    modules = {item["module"]: item for item in REGISTRY["modules"]}
    for path in (VERIFICATION / "Rowl").rglob("*.lean"):
        if "Generated" in path.parts:
            continue
        source = path.read_text()
        # These project sources use ordinary block and line comments. The Lean
        # checker/axiom audit remains the authority, including private helpers.
        code = re.sub(r"/-.*?-/|--[^\n]*", "", source, flags=re.S)
        if re.search(r"\b(?:sorry|admit)\b|(?m:^\s*(?:axiom|opaque|unsafe)\s)", code):
            raise RuntimeError(f"Unproved declaration in {path.relative_to(ROOT)}")
        exported = re.findall(r"(?m)^theorem\s+(\w+)", source)
        module = ".".join(path.relative_to(VERIFICATION).with_suffix("").parts)
        if exported:
            if module not in modules:
                raise RuntimeError(f"Unaudited proof module: {module}")
            item = modules[module]
            names = [item["namespace"] + "." + name for name in exported]
            if names != item["theorems"]:
                raise RuntimeError(f"Public theorem audit registry is stale: {module}")
    audit_names = re.findall(r"(?m)^#print axioms (\S+)", (VERIFICATION / "Rowl/Audit.lean").read_text())
    if audit_names != AUDITED:
        raise RuntimeError("Audit.lean does not match the declaration registry")


def check_model_inventory():
    inventory = json.loads((ROOT / "docs/model-inventory.json").read_text())
    rust = (ROOT / "crates/rowl-kernel/src/model.rs").read_text()
    semantics = (VERIFICATION / "Rowl/OwlSemantics.lean").read_text()
    for name, expected in inventory["enums"].items():
        block = re.search(r"pub enum " + name + r"\s*\{(.*?)^\}", rust, re.S | re.M)
        actual = re.findall(r"(?m)^    ([A-Z]\w*)\b", block.group(1)) if block else []
        if actual != expected:
            raise RuntimeError(f"Structural constructor inventory is stale: {name}")
        if name in inventory["semantic_matches"]:
            function = inventory["semantic_matches"][name]
            meaning = re.search(r"^def " + function + r"\b.*?(?=^def |^theorem |^termination_by|\Z)",
                                semantics, re.S | re.M)
            cases = re.findall(r"(?m)^  \| \.([A-Z]\w*)", meaning.group(0)) if meaning else []
            if cases != expected:
                raise RuntimeError(f"Semantic constructor coverage is stale: {name}")
    collection = (VERIFICATION / "Rowl/Collection.lean").read_text()
    for name, function in inventory["collection_matches"].items():
        meaning = re.search(r"^def " + function + r"\b.*?(?=^def |^theorem |^termination_by|\Z)",
                            collection, re.S | re.M)
        cases = re.findall(r"(?m)^  \| \.([A-Z]\w*)", meaning.group(0)) if meaning else []
        if cases != inventory["enums"][name]:
            raise RuntimeError(f"Entity collection constructor coverage is stale: {name}")
    anonymous = (VERIFICATION / "Rowl/Anonymous.lean").read_text()
    for name, function in inventory["anonymous_matches"].items():
        meaning = re.search(r"^def " + function + r"\b.*?(?=^def |^private |^theorem |^termination_by|\Z)",
                            anonymous, re.S | re.M)
        cases = re.findall(r"(?m)^  \| \.([A-Z]\w*)", meaning.group(0)) if meaning else []
        if cases != inventory["enums"][name]:
            raise RuntimeError(f"Anonymous positional coverage is stale: {name}")
    print("Constructor inventories valid: 18 class forms, 6 data ranges, 37 axioms; exhaustive meanings, entity collection and anonymous positions.", flush=True)


def check_builtin_inventory():
    inventory = json.loads((ROOT / "docs/builtin-vocabulary.json").read_text())
    expected = [(entry["iri"], entry["kind"]) for entry in inventory["entities"]]
    if len(expected) != 49 or len({iri for iri, _ in expected}) != 49:
        raise RuntimeError("The normative built-in declaration inventory must have 49 distinct IRIs")
    rust = (ROOT / "crates/rowl-kernel/src/builtins.rs").read_text()
    actual = re.findall(r'same_pattern\(\s*key,\s*b"([^"]+)"\s*,?\s*\).*?Some\(EntityKind::(\w+)\)', rust, re.S)
    if actual != expected:
        raise RuntimeError("Rust built-in roles do not match the reviewed vocabulary")
    lean = (VERIFICATION / "Rowl/Builtins.lean").read_text()
    formal = []
    for values, kind in re.findall(r"\(\[([0-9#u8, ]+)\], \.(\w+)\)", lean):
        formal.append((bytes(int(value) for value in re.findall(r"(\d+)#u8", values)).decode("utf-8"), kind))
    if formal != expected:
        raise RuntimeError("Formal built-in roles do not match the reviewed vocabulary")
    prefixes = inventory["reserved_prefixes"]
    if prefixes != ["http://www.w3.org/1999/02/22-rdf-syntax-ns#",
                    "http://www.w3.org/2000/01/rdf-schema#",
                    "http://www.w3.org/2001/XMLSchema#",
                    "http://www.w3.org/2002/07/owl#"]:
        raise RuntimeError("The reserved-prefix inventory differs from OWL 2 Table 2")
    vocabulary = (ROOT / "crates/rowl-kernel/src/vocabulary.rs").read_text()
    actual_prefixes = re.findall(r'prefix_from\(key,\s*b"([^"]+)"', vocabulary)
    if actual_prefixes != prefixes:
        raise RuntimeError("Rust reserved prefixes differ from the reviewed vocabulary")
    formal_source = (VERIFICATION / "Rowl/Vocabulary.lean").read_text()
    formal_prefixes = [bytes(int(value) for value in re.findall(r"(\d+)#u8", values)).decode("utf-8")
                       for values in re.findall(r"^  \[([0-9#u8, ]+)\]", formal_source, re.M)]
    if formal_prefixes != prefixes:
        raise RuntimeError("Formal reserved prefixes differ from the reviewed vocabulary")
    print("Built-in inventory valid: 49 declaration IRIs and 4 reserved prefixes; datatype value semantics remain pending.", flush=True)


def check_functional_inventory():
    inventory = json.loads((ROOT / "docs/functional-terminals.json").read_text())
    keywords = inventory["keywords"]
    if len(keywords) != 71 or len(set(keywords)) != 71:
        raise RuntimeError("Functional Syntax requires exactly 71 distinct keyword terminals")
    if inventory["punctuation"] != ["(", ")", "=", "^^"]:
        raise RuntimeError("Functional Syntax punctuation inventory differs from the complete grammar")
    if inventory["variable_terminals"] != ["nonNegativeInteger", "quotedString", "languageTag",
                                            "nodeID", "fullIRI", "prefixName", "abbreviatedIRI"]:
        raise RuntimeError("Functional Syntax variable-terminal inventory is incomplete")
    if inventory["special_terminals"] != ["whitespace", "comment"]:
        raise RuntimeError("Functional Syntax special-terminal inventory is incomplete")
    rust = (ROOT / "crates/rowl-frontend/src/functional.rs").read_text()
    enum = re.search(r"pub enum Keyword\s*\{(.*?)^\}", rust, re.S | re.M)
    if not enum or re.findall(r"(?m)^    (\w+),", enum.group(1)) != keywords:
        raise RuntimeError("Rust keyword constructors differ from the reviewed complete grammar")
    actual = re.findall(r'Keyword::(\w+)\s*=>\s*literal\(b"([^"]+)"\)', rust)
    if actual != [(word, word) for word in keywords]:
        raise RuntimeError("Rust keyword spellings differ from the reviewed complete grammar")
    formal = (VERIFICATION / "Rowl/Functional.lean").read_text()
    expected = re.findall(r'^  \| \.(\w+) => "([^"]+)"\.toList\.map Char\.toNat', formal, re.M)
    if expected != [(word, word) for word in keywords]:
        raise RuntimeError("Independent keyword spellings differ from the reviewed complete grammar")
    # The complete raw representation must be reachable through actual syntax.
    model = json.loads((ROOT / "docs/model-inventory.json").read_text())["enums"]
    required = set(model["ClassExpression"]) | set(model["Axiom"])
    required |= {"DataIntersectionOf", "DataUnionOf", "DataComplementOf", "DataOneOf",
                 "DatatypeRestriction", "ObjectPropertyChain", "ObjectInverseOf", "Prefix",
                 "Ontology", "Import", "Datatype", "ObjectProperty", "DataProperty",
                 "AnnotationProperty", "NamedIndividual", "Annotation"}
    if required != set(keywords):
        raise RuntimeError("Functional Syntax keywords do not cover the complete raw OWL model")
    selection = rust.split("pub fn next_terminal", 1)[1]
    selected = re.findall(r"Terminal::(?:Keyword\(Keyword::(\w+)\)|(\w+))", selection)
    expected_kinds = [(word, "") for word in keywords] + [("", kind) for kind in
        ["Open", "Close", "Equals", "DatatypeIndicator", "Integer", "QuotedString",
         "LanguageTag", "NodeId", "FullIri", "PrefixName", "AbbreviatedIri", "Whitespace", "Comment"]]
    if selected != expected_kinds:
        raise RuntimeError("Actual combined selector does not visit the complete standard inventory")
    selection_spec = (VERIFICATION / "Rowl/FunctionalSelection.lean").read_text()
    selected_keywords = re.findall(r"^  \.Keyword \.(\w+)", selection_spec, re.M)
    selected_other = re.findall(r"^  \.(\w+)(?:,|\])", selection_spec, re.M)
    if selected_keywords != keywords or selected_other != [kind for _, kind in expected_kinds if kind]:
        raise RuntimeError("Formal combined-selection inventory differs from the reviewed complete grammar")
    print("Functional terminal inventory valid: 71 keywords, 4 punctuation, 7 variable and 2 special classes; full lexer/parser composition remains pending.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true", help="Update generated Lean and source hashes before checking proofs")
    arguments = parser.parse_args()
    environment = os.environ.copy()
    environment["PATH"] = os.pathsep.join([str(Path.home() / ".cargo/bin"), str(Path.home() / ".elan/bin"), environment["PATH"]])
    environment["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    check_inventory()
    check_proof_sources()
    check_model_inventory()
    check_builtin_inventory()
    check_functional_inventory()
    aeneas = ROOT / ".tools/aeneas/aeneas"
    charon = ROOT / ".tools/aeneas/charon"
    if not aeneas.exists() or not charon.exists():
        raise SystemExit("Missing pinned tools. Run python3 scripts/bootstrap.py first.")
    version = run([aeneas, "-version"], environment, capture=True).strip()
    if version != "aeneas " + PINS["aeneas"]["release"]:
        raise RuntimeError(f"Wrong Aeneas version: {version}")
    receipt = ROOT / ".tools/aeneas/.rowl-sha256"
    if not receipt.exists() or receipt.read_text().strip() != PINS["aeneas"]["sha256"]:
        raise RuntimeError("Missing hash-checked Aeneas installation receipt; rerun bootstrap.py")
    source_hashes = VERIFICATION / "source-hashes.json"
    with tempfile.TemporaryDirectory(prefix="rowl-verification-") as temporary:
        staging = Path(temporary)
        extraction_environment = environment | {"RUSTUP_TOOLCHAIN": PINS["extraction_rust"]}
        for extraction in PINS["extractions"]:
            intermediate = staging / (extraction["crate"].replace("-", "_") + ".llbc")
            manifest = ROOT / "crates" / extraction["crate"] / "Cargo.toml"
            run([charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--dest-file", intermediate,
                 "--", "--manifest-path", manifest, "--lib"], extraction_environment)
            run([aeneas, "-backend", "lean", "-namespace", extraction["namespace"], "-dest", staging,
                 "-subdir", "Rowl/Generated", "-loops-to-rec", "-no-progress-bar", "-warnings-as-errors", intermediate], environment)
            generated = staging / "Rowl/Generated" / extraction["file"]
            expected = VERIFICATION / "Rowl/Generated" / extraction["file"]
            check_generated(generated.read_text())
            if arguments.regenerate:
                expected.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(generated, expected)
            elif not expected.exists() or generated.read_bytes() != expected.read_bytes():
                raise RuntimeError(f"Generated Lean is stale: {extraction['crate']}; regenerate and repair proofs")
        hashes = linkage()
        if arguments.regenerate:
            source_hashes.write_text(json.dumps(hashes, indent=2, sort_keys=True) + "\n")
        if not source_hashes.exists() or json.loads(source_hashes.read_text()) != hashes:
            raise RuntimeError("Source linkage is stale; regenerate and recheck proofs")
    if not (VERIFICATION / "lake-manifest.json").exists() or not (VERIFICATION / ".lake/packages/mathlib/.git").exists():
        run(["lake", "update"], environment, VERIFICATION)
    lean_version = run(["lake", "env", "lean", "--version"], environment, VERIFICATION, capture=True)
    expected_lean = PINS["lean"].split(":v", 1)[1]
    if f"version {expected_lean}," not in lean_version:
        raise RuntimeError(f"Wrong Lean toolchain: {lean_version.strip()}")
    check_dependency_pins()
    # Cache only the proof dependency closure instead of all of mathlib.
    cache_roots = mathlib_cache_roots()
    cache_key = hashlib.sha256(json.dumps(cache_roots).encode()).hexdigest() + digest(VERIFICATION / "lake-manifest.json")
    cache_receipt = VERIFICATION / ".lake/cache-ready"
    if not cache_receipt.exists() or cache_receipt.read_text() != cache_key:
        run(["lake", "exe", "cache", "get", *cache_roots], environment, VERIFICATION)
        cache_receipt.write_text(cache_key)
    run(["lake", "build"], environment, VERIFICATION)
    audit = run(["lake", "env", "lean", "-DwarningAsError=true", "Rowl/Audit.lean"], environment, VERIFICATION, capture=True)
    check_axioms(audit)
    print(f"Verified registered scope: {len(THEOREMS)} theorem audits and {len(REGISTRY['specifications'])} semantic-definition audits; full M3/M4 and OWL decisions remain pending.", flush=True)


if __name__ == "__main__":
    main()
