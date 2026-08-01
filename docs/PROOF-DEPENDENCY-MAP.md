# Brockian Proof Dependency Map

This document is a registry-backed map of the current proof surface. It uses
`registry/theorems.json`, `REGISTRY.md`, `Brockian.lean`, and
`provenance/verdicts.yaml` as sources of record. It is descriptive only: it does
not upgrade any `CONDITIONAL` or `CONJECTURE` entry into a proved theorem.

## Current Registry Summary

The registry is generated from AXLE attestations. `REGISTRY.md` states that
`PROVED` entries include kernel-checked finite `decide` results and exclude
`native_decide` from `PROVED` by the axiom gate; `DEFINITION` entries are
supporting definitions; `CONJECTURE` entries are named Prop containers rather
than claims.

Current counts:

| Register | Count |
|---|---:|
| `PROVED` | 695 |
| `DEFINITION` | 182 |
| `CONDITIONAL` | 10 |
| `CONJECTURE` | 1 |

All remaining `CONDITIONAL` and `CONJECTURE` entries are AXLE-verified in
`lean-4.32.0`, axiom-clean under the registry gate, have no `sorry`, have no
`native_decide`, and are quarantined by provenance. Their register is determined
by the open premise/container discipline, not by AXLE failure.

## Public Import Surface

`Brockian.lean` imports 60 modules. The import list is a public aggregation
surface, not by itself a mathematical dependency proof. The relevant clusters are:

- Arithmetic, sieve, singular series, and Goldbach: `Admissibility`,
  `AdmissibilityCRT`, `TransitionKernel`, `Sieve`, `SingularSeries`,
  `SingularSeriesConvergence`, `GoldbachComb`, `GoldbachSchema`,
  `GoldbachLemmas`, `GoldbachParity`, and `EquidistributionSchema`.
- Pentagon, D5, and finite algebra: `Core`, `Geometry`, `Spectral`,
  `Connectivity`, `CycleSpectrumFamily`, `Automorphism`, `AutomorphismFull`,
  `D5Representation`, `D5Isotypic`, `AffineSymmetry`, and `MetallicFamily`.
- Spectral/Weyl/RH scaffold: `SpectralGate1`, `RiemannScaffold`, the imported
  `Weyl*` modules, and `PenroseL2`.

## Remaining Open Registry Entries

| Register | Declaration | Registry boundary |
|---|---|---|
| `CONDITIONAL` | `Brockian.Equidistribution.equidistribution_of_asymptotic` | Depends on `PrimePairAsymptotic`, an HL/BV-strength uniform per-config asymptotic premise. The registry marks the premise open and not instantiable. |
| `CONDITIONAL` | `Brockian.Equidistribution.equidistribution_of_asymptotic_exists` | Existence of an HL/BV asymptotic structure implies equidistribution; the existence premise is the open schema. |
| `CONJECTURE` | `Brockian.GoldbachComb.GoldbachCovarianceTransfer` | Named transfer conjecture / Prop container. The registry says it is never a claimed theorem. |
| `CONDITIONAL` | `Brockian.GoldbachSchema.goldbach_from_spectral_model` | `SpectralModel -> Goldbach beyond N0`; the spectral-model instantiation is Goldbach-strength and open. |
| `CONDITIONAL` | `Brockian.GoldbachSchema.goldbach_beyond_of_model` | Existence of the model implies Goldbach beyond `N0`; the model existence is the open hardness direction. |
| `CONDITIONAL` | `Brockian.RiemannScaffold.RH_of_BrockianSystem` | A Hilbert-Polya-strength `BrockianSystem` with the required real-spectrum and zeros-to-spectrum fields implies RH; the system is open and not shown instantiable. |
| `CONDITIONAL` | `Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity` | Reduces the concrete deficiency-to-ODE representation to `WeakSolutionRegularity`, a named 1D elliptic-regularity input absent from Mathlib. |
| `CONDITIONAL` | `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity` | Concrete Schrodinger ESA follows from the same weak-regularity input plus the already proved deficiency/Bridge plumbing. |
| `CONDITIONAL` | `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier` | `-Delta` ESA depends on a Fourier unitary intertwining with unbounded `xi^2` multiplication and ESA for that unbounded model. |
| `CONDITIONAL` | `Brockian.Weyl.KatoUnbounded.essentiallySelfAdjoint_perturb` | `T+B` ESA depends on `BoundedPerturbationTransfer`, the unbounded range-density transfer. |
| `CONDITIONAL` | `Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode` | Concrete `-d^2/dx^2+V` ESA depends on `deficiencyRepresentsODE`, the elliptic-regularity/ODE-identification input. |

## Dependency Graph Narrative

### Gate 1: Spectral/Weyl Operator Chain

The bounded Gate 1 branch starts at `Brockian.SpectralGate1`, whose registry
entries prove boundedness, summability, continuity, and self-adjointness facts
for the prime-Gaussian multiplication operator. `provenance/verdicts.yaml`
describes this as an honest bounded-potential multiplication-operator rung and
explicitly leaves unbounded `-Delta+V` essential self-adjointness open.

`Brockian.Weyl.Gate1Bounded` imports `SpectralGate1`, `WeylEssSelfAdjoint`,
`WeylKato`, and `WeylOperator`. Its registry note proves the prime-Gaussian
bounded-potential ESA and dense-range statements for non-real shifts, plus
bounded self-adjoint perturbation facts. It is not the full `-Delta+V` result.

The unbounded route is split into named open inputs. `Weyl.FreeLaplacian2`
contains the transfer core and bounded/multiplication model facts, but its
free-Laplacian theorem is conditional on Fourier/unbounded-multiplier inputs.
`Weyl.KatoUnbounded` proves bounded-case and structural perturbation facts, but
the unbounded perturbation theorem remains conditional on
`BoundedPerturbationTransfer`. `Weyl.Bridge` proves the non-real L2 solution
vanishing identity, but the provenance says this does not alone construct the
operator or prove ESA. `Weyl.SchrodingerESA` assembles Bridge + Cayley under
`DeficiencyRepresentsODE`, and `Weyl.SchrodingerMinimal` reduces the concrete
Schrodinger operator to the one named elliptic-regularity premise.
`Weyl.DeficiencyODE` narrows that premise further: the concrete
deficiency-to-ODE representation and the corresponding Schrodinger ESA theorem
are conditional on `WeakSolutionRegularity`, the classical 1D weak-solution
regularity fact not yet present in Mathlib.

`Weyl.Confining` is a shape audit for the RH-operator direction: the registry
records that bounded/decaying prime-Gaussian operators miss large zeta zeros and
that an unbounded shape is needed. Its provenance explicitly says it does not
claim ESA or discrete spectrum.

### Singular Series and Goldbach

The local-count branch starts with `Brockian.Admissibility`, which records the
`q-nu` admissibility law, and `Brockian.Admissibility.CRT`, which records the
plain CRT product count for coprime moduli. `Brockian.SingularSeries` provides
local-factor positivity and summability data, while
`Brockian.SingularSeries.Convergence` records the infinite-product convergence
rung that discharges the old `h_conv` input and gives `singular_series_pos'`
unconditionally.

The Goldbach branch is deliberately split between unconditional local arithmetic
and open global transfer. `GoldbachLemmas` contains Hardy-Littlewood factor and
local-density lemmas; `Goldbach.Parity` contains elementary parity and local
count facts and imports the comb, lemmas, and schema. `GoldbachComb` records the
exact local covariance kernel, but its named covariance-transfer declaration is
the one remaining `CONJECTURE`.

`GoldbachSchema` is the global conditional layer. It uses real prime-pair counts
and proves base cases, but the two Goldbach declarations in the registry are
open schemas: they require a `SpectralModel`/model existence input that the
registry marks as Goldbach-strength. `Equidistribution` is similarly conditional:
it proves support and shape-consistency facts, but its two equidistribution
entries require an HL/BV-strength asymptotic premise.

### D5 and Pentagonal Finite Algebra

This cluster has no remaining `CONDITIONAL` or `CONJECTURE` entries in the
current registry. `Core` records the phi stack, ray ring, Binet, roots of unity,
and Dirichlet-on-rays anchors. `Geometry` records the pentagon golden diagonal,
two-distance facts, and `-phi` in the `C5` spectrum. `Spectral` records
`phi-1 in spec(C_p) iff p=5`, and `Connectivity` records the golden algebraic
connectivity value for `C5`. `CycleSpectrumFamily` generalizes cycle-spectrum
facts and states the golden rigidity only at the level already recorded by the
registry.

The D5 automorphism branch is now staged. `Automorphism` contains the faithful
`D5 -> Aut(C5)` action and explicit rotation/reflection facts; `AutomorphismFull`
records the reverse bound, cardinality equality, surjectivity, and full
`Aut(C5) ~= D5` equivalence. Downstream, `D5Representation` records the finite
vertex-space pullback action, invariant constants, invariant coordinate sum, and
zero-sum hyperplane invariance. `D5Isotypic` sits on that representation branch
and records eigenmode, primitive-root, character-orthogonality, and
isotypic-projector facts.

`AffineSymmetry` is a separate finite-algebra correction: it distinguishes
additive automorphisms of `ZMod p`, graph automorphisms of cycle graphs, and the
affine-dihedral subgroup. `MetallicFamily` connects metallic means back to the
verified golden/spectral and sieve facts.

### RH Scaffold

`Brockian.RiemannScaffold` has seven registry entries: four `PROVED`, two
`DEFINITION`, and one `CONDITIONAL`. The unconditional part is the xi-function
bridge: `riemannXi`, Gamma-factor nonvanishing for nontrivial zeros, transfer
from zeta zeros to xi zeros, `xi`-RH to Mathlib RH, and the symmetric-operator
real-eigenvalue fact. The registry explicitly says RH is not claimed.

The sole conditional RH entry is `RH_of_BrockianSystem`. Its dependency is not a
proved Brockian operator; it is the Hilbert-Polya-strength `BrockianSystem`
structure with dense symmetric operator, real-spectrum, and zeros-to-spectrum
fields. `Weyl.Confining` and `Weyl.OperatorChoice` support the operator-choice
audit by recording that the current bounded prime-Gaussian branch cannot be the
RH operator shape. The registry therefore leaves the RH scaffold as an honest
conditional implication plus bounded-operator obstruction facts, not RH progress.
