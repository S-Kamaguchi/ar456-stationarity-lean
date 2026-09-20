# ar456-stationarity-lean

Lean 4 / Mathlib formal verification companion to the paper
**"Explicit Stationarity Regions for AR(4), AR(5), and AR(6) via Unit-Circle Analysis."**

This repository contains machine-checked proofs of the paper's formal propositions and
lemmas, including:

- Full necessary-and-sufficient-condition proofs for AR(3) through AR(6)
  (`StTopology/AR3.lean`, `AR4.lean`/`AR4Sufficiency.lean`, `AR5.lean`/`AR5Sufficiency.lean`,
  `AR6.lean`/`AR6Sufficiency.lean`).
- The topological structure result of Section 3.9: the stationarity region $St(p)$ is
  homeomorphic to an open Euclidean ball, with its boundary homeomorphic to the sphere
  $S^{p-1}$ (`Mu.lean`, `Nu.lean`, `RadialCoordinate.lean`, `Xi.lean`, `CrystalBall.lean`).
- The general-degree results of Section 4.7: the two-step Step-down merge identity
  (`TwoStepMerge.lean`) and the $\lceil p/2\rceil$ bound on the number of explicit
  closed-form inequalities needed to describe $St(p)$ (`StepDown.lean`, `CountBound.lean`).
- The elementary structural properties of Section 3.1-3.6: zero-extension scalability
  (`ZeroExt.lean`), coefficient sign symmetry (`SignSym.lean`), dimensional multiplicity
  (`DimMult.lean`), the Eneström-Kakeya criterion (`Kakeya.lean`, including a from-scratch
  proof of the classical Eneström-Kakeya theorem itself), and the Gauss-Lucas reduction
  (`GaussLucas.lean`).

## Status

- **`sorry`-free**: the entire repository builds with zero `sorry` statements.
- Verified with `lake build` (Lean toolchain pinned in `lean-toolchain`; dependencies pinned
  in `lake-manifest.json`).

## Scope note

This repository formalizes the paper's rigorous propositions, lemmas, and named structural
results. It is a proof-assistant companion to the paper, not a substitute for it: the paper
contains the full mathematical exposition, motivation, numerical verification (a separate
companion repository, see below), and discussion.

## Relation to other companion material

Numerical verification of the explicit stationarity conditions against direct root
computation is provided in a separate repository:
[ar456-stationarity-code](https://github.com/S-Kamaguchi/ar456-stationarity-code).

## Building

```
lake build
```

## Citation

If you use this formalization, please cite the paper. Citation details for this repository
itself will be added once archived (see below).
