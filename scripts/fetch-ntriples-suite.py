#!/usr/bin/env python3
"""Fetch the exact official W3C syntax corpus used by the N-Triples regressions.

The files remain external test data. This tool does not feed the proof kernel.
Usage: python3 scripts/fetch-ntriples-suite.py /tmp/rowl-ntriples-suite
"""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("destination", type=Path)
args = parser.parse_args()
metadata = json.loads((Path(__file__).resolve().parents[1] / "docs/ntriples-suite.json").read_text())
args.destination.mkdir(parents=True, exist_ok=True)


def fetch(item):
    name, expected = item
    target = args.destination / name
    if not target.exists():
        # A total transfer deadline also covers servers that trickle bytes.
        download = subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                                   "--max-time", "40", metadata["source"] + name],
                                  check=True, capture_output=True)
        contents = download.stdout
        if hashlib.sha256(contents).hexdigest() != expected:
            raise RuntimeError(f"Official test data changed: {name}")
        target.write_bytes(contents)
    if hashlib.sha256(target.read_bytes()).hexdigest() != expected:
        raise RuntimeError(f"Unexpected test data: {target}")
    return name


with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    for name in pool.map(fetch, metadata["files"].items()):
        print(f"Checked {name}", flush=True)
print(f'Exact W3C corpus ready: {metadata["syntax_case_count"]} syntax cases.')
