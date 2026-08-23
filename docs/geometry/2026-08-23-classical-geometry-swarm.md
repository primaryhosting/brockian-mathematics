# Classical Geometry Swarm v1

`benchmarks/classical-geometry-swarm.yaml` is a small, executable benchmark
ledger for source-guided geometry work. It is intentionally not a source of new
theorem claims and it never contributes to the Brockian novelty ledger.

## What it changes

Each task moves through five required and separately auditable stages:

| Stage | Role | Acceptable evidence |
| --- | --- | --- |
| Explore | Explorer | Exact-coordinate or symbolic construction plus an attempted falsifier |
| Formalize | Specifier | A Lean-ready statement with all hypotheses visible |
| Prove | Prover | Sorry-free Lean source and exact environment plan |
| Attack | Adversary | Degeneracy, sign, denominator, boundary, and convention checks |
| Audit | Auditor | Source, computation, proof, and unresolved-obligation provenance |

The deterministic dispatcher is:

```bash
python3 scripts/geometry_swarm_plan.py --track signed-ceva-menelaus-projective-extension
```

It generates a task packet; it cannot create or promote a theorem. The blocking
validator is:

```bash
python3 scripts/validate_geometry_swarm.py
```

## Source evaluation

| Source | Best leverage | Priority | Boundary |
| --- | --- | --- | --- |
| Venema, *Exploring Advanced Euclidean Geometry* (2006) | The explicit distinction between dynamic verification and proof; signed-ratio Ceva/Menelaus; accessible Poincare-disk constructions | P0 workflow and P0 projective extension | A moving diagram is exploration evidence, never proof. |
| Yiu, *Advanced Euclidean Geometry* (2013) | Direct regular-pentagon/golden-ratio construction (pp. 106-107), followed by Menelaus/Ceva (pp. 201-204) and homogeneous barycentrics/infinite points (pp. 301-314) | P0 pentagon and Ceva/Menelaus; P1 barycentrics | These are classical results and remain excluded from novelty accounting. |
| Coxeter, *Non-Euclidean Geometry*, 5th ed. (1965) | Projective foundations, polarity, Klein model, and Poincare model | P1 foundation/model card | A hyperbolic model is not evidence of a phase-depth or gauge correspondence without an explicit map and theorem. |

## Current baseline and next work

The repository already has green, independently attested baselines for
`Brockian.MsCeva.ceva`, `Brockian.MsMenelaus.menelaus`,
`Brockian.Geometry.pentagon_golden_diagonal`, and
`Brockian.Geometry.golden_ratio_in_C5_spectrum`. The benchmark does not claim
that these settle directed ratios, zero denominators, ideal points, or a full
projective extension.

The first dispatch should be the signed Ceva/Menelaus track. It has the clearest
formal delta: first define an orientation-safe ratio and an ideal-point interface;
then prove a precise extension or record the exact missing Mathlib API. The
Poincare/Klein track should start only after that projective vocabulary is stable.

Source PDFs remain user-provided private references. The repository records only
metadata, hashes, and short page locators; it does not redistribute their text or
figures.
