#!/usr/bin/env python3
"""Install hash-pinned local Aeneas and exact Rust/Lean toolchains.

Build infrastructure, not ontology semantics. No administrative privileges.
The prebuilt Aeneas bundle currently targets Linux x86_64 only.
"""

import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / ".tools"
PINS = json.loads((ROOT / "verification/toolchain.json").read_text())


def digest(path):
    with path.open("rb") as contents:
        return hashlib.file_digest(contents, "sha256").hexdigest()


def download(pin, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.exists() or digest(destination) != pin["sha256"]:
        print(f"Downloading {destination.name}", flush=True)
        temporary = destination.with_suffix(destination.suffix + ".part")
        with urllib.request.urlopen(pin["url"], timeout=60) as response, temporary.open("wb") as output:
            shutil.copyfileobj(response, output)
        if digest(temporary) != pin["sha256"]:
            raise RuntimeError(f"SHA-256 mismatch: {destination.name}")
        temporary.replace(destination)
    return destination


def run(*arguments, **kwargs):
    print("+ " + " ".join(map(str, arguments)), flush=True)
    subprocess.run(list(map(str, arguments)), check=True, **kwargs)


def extract(archive, destination):
    destination.mkdir(parents=True, exist_ok=True)
    # All archive bytes must first match the pinned digest. data blocks path traversal.
    with tarfile.open(archive) as contents:
        contents.extractall(destination, filter="data")


def main():
    if sys.version_info < (3, 12):
        raise SystemExit("Bootstrap requires Python 3.12 or newer.")
    if (platform.system(), platform.machine()) != ("Linux", "x86_64"):
        raise SystemExit("Pinned binary bootstrap supports Linux x86_64. See architecture.md for the broader target; build the pinned upstream tools on other hosts.")
    cargo_bin = Path.home() / ".cargo/bin"
    elan_bin = Path.home() / ".elan/bin"
    environment = os.environ.copy()
    environment["PATH"] = os.pathsep.join([str(cargo_bin), str(elan_bin), environment["PATH"]])
    if not (cargo_bin / "rustup").exists():
        installer = download(PINS["rustup_installer"], TOOLS / "downloads/rustup-init")
        installer.chmod(0o755)
        run(installer, "-y", "--profile", "minimal", "--default-toolchain", "none", "--no-modify-path", env=environment)
    if not (elan_bin / "elan").exists():
        archive = download(PINS["elan_installer"], TOOLS / "downloads/elan.tar.gz")
        extract(archive, TOOLS / "elan-installer")
        run(TOOLS / "elan-installer/elan-init", "-y", "--default-toolchain", "none", "--no-modify-path", env=environment)
    run(cargo_bin / "rustup", "toolchain", "install", PINS["rust"], "--profile", "minimal", "--component", "rustfmt", "--component", "clippy", env=environment)
    run(cargo_bin / "rustup", "toolchain", "install", PINS["extraction_rust"], "--profile", "minimal", "--component", "rust-src", "--component", "rustc-dev", "--component", "llvm-tools", env=environment)
    run(elan_bin / "elan", "toolchain", "install", PINS["lean"], env=environment)
    archive = download(PINS["aeneas"], TOOLS / "downloads/aeneas.tar.gz")
    receipt = TOOLS / "aeneas/.rowl-sha256"
    if not receipt.exists() or receipt.read_text().strip() != PINS["aeneas"]["sha256"]:
        extract(archive, TOOLS / "aeneas")
        receipt.write_text(PINS["aeneas"]["sha256"] + "\n")
    run(TOOLS / "aeneas/aeneas", "-version", env=environment)
    print("Bootstrap complete. Run python3 scripts/verify.py.", flush=True)


if __name__ == "__main__":
    main()
