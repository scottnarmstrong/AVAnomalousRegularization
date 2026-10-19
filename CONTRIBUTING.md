# Contributing

This repository formalizes S. Armstrong and V. Vicol, *Anomalous regularization of passive scalars
up to the Obukhov–Corrsin exponent* ([doc/paper.pdf](doc/paper.pdf)), in Lean 4 and Mathlib, on top
of the [formalization of *Anomalous diffusion by fractal homogenization*](https://github.com/scottnarmstrong/AVAnomalousDiffusion).
The public statements are in [AVRegularity/Statements](AVRegularity/Statements): the main results
in `Main`, one theorem per file, the definitions they use in `Definitions` and `Construction`, and
intermediate results in `Intermediate`. Their proofs are in [AVRegularity/Proofs](AVRegularity/Proofs),
and the supporting library is in the other directories of [AVRegularity](AVRegularity).

## Development environment

Install the pinned toolchain and obtain the Mathlib cache:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
lake build
```

Keep the committed `lake-manifest.json`, which pins Mathlib and the formalization of *Anomalous
diffusion by fractal homogenization* at exact commits. Avoid `lake update` and `lake clean` when
verifying this version: they can change dependencies or remove the build cache. The first build
compiles this library and that dependency from source, which takes about 9.6 CPU-hours (about 8.7
for this library and 0.9 for the dependency), about 1.5 hours of wall time with six parallel
compiles.

## Lean source conventions

Lean files begin with the notice

```lean
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
```

followed by the `module` header. All Lean files use Lean's module system. A file imports the
modules whose declarations it uses, and imports a module `public`ly only when its statements or
exposed definitions need it; never import all of Mathlib.

Library code contains no `sorry`, `admit` or custom axiom; the only intentional `sorry`s are the
theorem bodies in [AVRegularityChallenge.lean](AVRegularityChallenge.lean), proved in
[AVRegularitySolution.lean](AVRegularitySolution.lean). Do not add heartbeat overrides
(`set_option maxHeartbeats`): a proof that does not elaborate within the default budget should be
split or restructured. Apart from the eleven `declaration uses sorry` warnings of the Challenge,
the build has no warnings; keep it so. Library files stay below 1,500 lines; split a file into
focused modules when it grows. The Challenge must stay below 1,000 lines and 100 KiB.

Changes to a statement in `AVRegularity/Statements`, or to a definition it uses, need mathematical
review against the paper, a matching change to `AVRegularityChallenge.lean` and
`AVRegularitySolution.lean`, and a matching entry in [doc/correspondence.md](doc/correspondence.md).

## Checking a change

From the repository root:

```sh
lake build
python3 scripts/check-lean-sources.py
python3 scripts/check-metadata.py
python3 scripts/check-axioms.py
scripts/verify-comparator.sh
```

For a new public theorem, add it to `scripts/Axioms.lean` and include its `#print axioms` output
with the change.
