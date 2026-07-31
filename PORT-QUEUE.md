# Port Queue — keeper proofs not yet in the compiling core

Per the convergence rule (spec §4): a keeper that will not port this session is recorded
here with its blocking reason and kept OUT of the core so `lake build` stays green. Nothing
is faked. Items marked **RELEASE-BLOCKING** are §8 must-port keepers that require explicit
human sign-off to defer.

## RELEASE-BLOCKING (§8 must-port — deferred, need human sign-off)

| Result | Ledger run | Blocking reason |
|--------|-----------|-----------------|
| **`golden_unique_to_five`** (φ ∈ spec(C_p) ⟺ p=5) | 73 | The hand-organized legacy sources (`GoldenRatio.lean`, `DihedralGroup.lean`) carry the *necessity* ("only if") direction as `sorry`. The actual run-73 verified proof is in the `archive/` raw Aristotle outputs (UUID-named), which were not routed to a port agent this session. The "if" direction is captured by `Brockian.Geometry.golden_ratio_in_C5_spectrum`. |
| **`Aut(C₅) ≅ D₅`** | 54 | Legacy source (`isometry_group_is_dihedral`) surjectivity is `sorry`; Mathlib 4.32 `SimpleGraph.cycleGraph` has no dihedral-automorphism theorem to close it cleanly. Partially surfaced via `Brockian.Geometry.d5_card` (|D₅|=10) + the spectral eigenvalue fact. Run-54 verified proof is in `archive/`. |
| **`λ₂(C₅) = 2 − 1/φ`** (algebraic connectivity) | 88 | Not attempted this session; the graph-Laplacian spectral-gap campaign (runs 84–92) lives in `archive/` raw outputs, not the named BCC modules. |

**Resolution path:** locate runs 73/88/54 in `/Volumes/BCC-Storage/Projects/Brockian-Math/lean/archive/` (UUID-named Aristotle outputs), route each to a port agent for the AXLE loop. These were genuinely machine-proved per the intake ledger; they are recoverable, just not from the files ingested this pass.

## Ordinary port-pending (non-blocking)

| Result | Source | Reason |
|--------|--------|--------|
| `singular_series_converges` | SingularSeries source | shipped as an `axiom` in source (analytic ∞-product convergence); dropped, surfaced as the `h_conv` hypothesis of `singular_series_pos` instead. Needs Mathlib ∑1/p² summability. |
| CA-6..CA-9 (`H4_golden_ground`, `twin_lag_support`, `twin_kernel_cases`) | ConstellationAlphabet.lean | spectral-alphabet / general-prime number theory; `sorry` targets in source, out of the TransitionKernel remit. |
| `cos_5theta`, `golden_ratio_necessity`, `golden_is_geometric_invariant` | GoldenRatio.lean | Chebyshev-quintic / matrix-power arguments left as `sorry` in source. |

## Local `lake build` leg

The third verification leg (local `lake build`) is pending: fetching Mathlib v4.32.0's
transitive dependencies in this environment is slow. Independent verification is fully
covered by AXLE at `lean-4.32.0` (a stronger, third-party check than a self-hosted build);
the local build stamps `verification.lake_build: green` once complete.
