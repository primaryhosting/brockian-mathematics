# Classical Geometry Swarm v2

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
| Viaclovsky, *218BC Introduction to Manifolds and Geometry* (2022) | The most build-ready bridge: vector-bundle transition cocycles, the trivial/Mobius line-bundle test on `S1`, finite group quotients, and de Rham computations | P0 cocycle fixture and comparison firewall; P1 quotient descent | Cover-dependent Cech calculations require a good cover or a proved refinement argument. |
| Cattaneo, *Notes on Manifolds* (2018) | The broad technical reference: charts, bundles, flows, tensors, differential forms, Stokes, symplectic geometry, and Lie groups | P0 atlas and exterior-derivative API work | Its coordinate proofs guide specifications; they should not be reimplemented when Mathlib already supplies the abstraction. |
| Hitchin, *Differentiable Manifolds* (2014) | The cleanest conceptual specification for closed/exact forms, de Rham cohomology, naturality, orientation, and geodesic flow | P0 de Rham specification; later Riemannian work | Conceptual similarity does not supply a formal comparison map. |

The second uploaded Coxeter file is byte-for-byte identical to the registered
copy (SHA-256
`8376cac530c1090c3ef3c3fd591f968f4e9923ae6bc66acae0e6409ab2f03ea1`).
It is deliberately not added as a seventh source. The benchmark validator now
rejects duplicate PDF hashes even when the duplicate is given a new source ID.

## Design decision from the manifold texts

The new material supports three related layers, but it does not yet prove that
the layers are equivalent:

| Layer | Object available to the build | Immediate use | Missing bridge obligation |
| --- | --- | --- | --- |
| Discrete | `ZMod 5` edge labels, coboundaries, total depth, and conjugacy-class holonomy | Existing finite phase-depth classification remains the green baseline | Choose a geometric realization and coefficient comparison. |
| Bundle/topological | Atlas or bundle transition functions satisfying overlap cocycle laws | Build the real line bundle over `S1`; use the trivial and Mobius bundles as positive/negative fixtures | Define a typed map from discrete edge labels to transition data and prove gauge compatibility. |
| Smooth | Differential forms, exterior derivative, closed/exact forms, and de Rham cohomology | Exercise Mathlib's `extDeriv` API and prove exact-implies-closed in the supported model-space setting | Construct a degree-preserving cochain map and prove it commutes with both differentials; prove any claimed quasi-isomorphism separately. |

This makes Viaclovsky's line-bundle example the highest-leverage design input:
it is small enough to formalize, has a genuine cocycle law, has both trivial and
nontrivial cases, and exposes cover mistakes quickly. Cattaneo is the best API
backstop, while Hitchin is the best source for concise theorem statements.

The hard boundary is deliberate: the repository's finite-cycle cohomology is
not de Rham cohomology. Reusing the symbol `H1`, observing that both settings
encode holonomy, or matching a dimension does not establish an equivalence.
The `discrete-to-de-rham-comparison-firewall` track makes the missing cochain map
and quasi-isomorphism obligations executable review criteria.

## Current baseline and next work

The repository already has green, independently attested baselines for
`Brockian.MsCeva.ceva`, `Brockian.MsMenelaus.menelaus`,
`Brockian.Geometry.pentagon_golden_diagonal`, and
`Brockian.Geometry.golden_ratio_in_C5_spectrum`. The benchmark does not claim
that these settle directed ratios, zero denominators, ideal points, or a full
projective extension.

For the manifold branch, the first dispatch should be
`exterior-derivative-square-zero`: Mathlib already exposes `extDeriv` and its
square-zero theorem, so this is the fastest way to validate imports, smoothness
indices, degrees, and the model-space/global-manifold boundary. Next, dispatch
`atlas-transition-cocycle`, then `real-line-bundle-cocycle-mobius`. The
`discrete-to-de-rham-comparison-firewall` must pass before either is described as
a phase-depth correspondence. `finite-quotient-descent` comes after a fixed-point
audit of the chosen `C5` or `D5` action.

The independent classical-geometry sequence is unchanged: signed
Ceva/Menelaus remains the clearest projective delta, and the Poincare/Klein track
should start only after that projective vocabulary is stable.

Source PDFs remain user-provided private references. The repository records only
metadata, hashes, and short page locators; it does not redistribute their text or
figures.
