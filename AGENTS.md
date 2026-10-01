# ROWL working instructions

Keep claims aligned with `docs/status.md`, `docs/coverage.json` and the checked
proof registry. Raw structure, independent semantic specification, executable
operations and a proved complete OWL reasoner are different deliverables.

For kernel/proof changes, run Rust formatting/Clippy/tests and
`python3 scripts/verify.py`. Use `--regenerate` after intentional source changes,
then check proofs and the normal freshness comparison. Do not introduce `sorry`,
admitted claims, custom semantic axioms or unsupported extraction assumptions.
Full OWL release requirements stay pending until their actual proofs pass.
