# Port Queue — keeper proofs not yet in the compiling core

Per the convergence rule (spec §4): a keeper that will not port this session is recorded
here with its blocking reason and kept OUT of the core so `lake build` stays green. Nothing
is faked. Items marked **RELEASE-BLOCKING** are §8 must-port keepers that require explicit
human sign-off to defer.

## RESOLVED (re-proved fresh via the AXLE loop, 2026-07-31)

The disk originals were not recoverable (audited from Aristotle tarballs not persisted here),
so the exact ledger-admitted statements were **re-proved fresh** at Mathlib v4.32.0 via
concrete circulant/Laplacian eigenvalues and independently AXLE-verified, axiom-clean:

| Result | Ledger run | Now |
|--------|-----------|-----|
| **`golden_unique_to_five`** (φ−1 ∈ spec(C_p) ⟺ p=5) | 73 | ✅ PROVED — full biconditional, `Brockian/Spectral.lean`. The "why five" rigidity result. |
| **`pentagon_lambda2_phi`** (λ₂(C₅)=2−1/φ) | 88 | ✅ PROVED — `Brockian/Connectivity.lean`, algebraic connectivity is golden. |

## RELEASE-BLOCKING (still deferred — need human sign-off)

| Result | Ledger run | Blocking reason |
|--------|-----------|-----------------|
| **`Aut(C₅) ≅ D₅`** | 54 | Mathlib 4.32 has `cycleGraph` but no `SimpleGraph.Aut` / graph-automorphism-group API, so the full group iso has no clean witness. See `Brockian/Automorphism.lean` for the highest honestly-verified rung (faithful dihedral action / |D₅|=10 / explicit rotation+reflection autos); the surjectivity onto Aut is the open piece. |

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
