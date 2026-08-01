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

## PARTIAL — honest strong partial shipped; one direction open

| Result | Ledger run | Status |
|--------|-----------|--------|
| **`Aut(C₅) ≅ D₅`** | 54 | ⬖ PARTIAL — `Brockian/Automorphism.lean` proves the faithful action `DihedralGroup 5 →* Aut(C₅)` injective, the explicit rotation/reflection automorphisms (adjacency preservation proved), and `10 ≤ |Aut(C₅)|`. **Open piece:** the reverse bound `|Aut(C₅)| ≤ 10` (which would give the full iso) — Mathlib 4.32 has no `SimpleGraph.Aut` enumeration / `Fintype (C₅ ≃g C₅)`, so it needs an explicit "an automorphism of a cycle is pinned by two adjacent images" argument. Not faked; the module claims only what it proves. |

## Ordinary port-pending (non-blocking)

| Result | Source | Reason |
|--------|--------|--------|
| `singular_series_converges` | SingularSeries source | shipped as an `axiom` in source (analytic ∞-product convergence); dropped, surfaced as the `h_conv` hypothesis of `singular_series_pos` instead. Needs Mathlib ∑1/p² summability. |
| CA-6..CA-9 (`H4_golden_ground`, `twin_lag_support`, `twin_kernel_cases`) | ConstellationAlphabet.lean | spectral-alphabet / general-prime number theory; `sorry` targets in source, out of the TransitionKernel remit. |
| `cos_5theta`, `golden_ratio_necessity`, `golden_is_geometric_invariant` | GoldenRatio.lean | Chebyshev-quintic / matrix-power arguments left as `sorry` in source. |

## Open frontier — the hard targets (attempted 2026-08-01, honestly open)

A swarm attacked Goldbach / Weyl / Riemann under strict anti-fakery discipline. None of the
open problems fell (as expected); every agent produced honest partials, no theater was found,
nothing was excluded. What genuinely verified is registered; what remains open is here.

| Target | Verified this round | Still open |
|--------|--------------------|-----------|
| **Weyl limit-point criterion** | Wronskian/Abel constancy, Lagrange + integrated Green identity, Gate-0 witness (`Brockian.Weyl`) | the criterion itself + essential self-adjointness of unbounded −Δ+V — Mathlib 4.32 has no Sturm–Liouville / deficiency-index / unbounded-`LinearPMap` self-adjointness API |
| **Goldbach** | `goldbach_from_spectral_model` (real implication, CONDITIONAL/open), singular-series factor lemmas, small base cases (`GoldbachSchema`, `GoldbachLemmas`) | instantiating a `SpectralModel` non-trivially — that is Goldbach-strength |
| **Riemann Hypothesis** | the ξ-bridge (unconditional: `riemannXi`, Γ-nonvanishing, ξ-zero-from-ζ-zero, ξ-RH ⇒ Mathlib RH), `RH_of_BrockianSystem` (CONDITIONAL/open) (`RiemannScaffold`) | inhabiting `BrockianSystem` — a densely-defined symmetric operator with real spectrum whose eigenvalues realise the ζ-zeros. Hilbert–Pólya-strength. Not shown instantiable, and (crucially) not provably empty — so the conditional is an honest open schema, not ex-falso |

The next honest, *achievable* step is the Weyl limit-point criterion (a classical theorem, not
an open problem): closing it would unconditionally discharge Gate 1's self-adjointness clause.
It is a Mathlib-infrastructure task, not a research gamble.

## Local `lake build` leg — environment-blocked (not a proof gap)

The dependency graph resolves (manifest + all 9 packages cloned), but `lake exe cache get`
returns success while downloading **no oleans** (the Mathlib cache CDN is unreachable from
this environment). `lake build` therefore falls back to compiling Mathlib **from source**
(~hours) and times out. So the local-build leg is stamped `lake_build: pending` in the
registry — honestly, not green.

This is an environment limitation, not a hole in the mathematics: **AXLE independently
verifies every PROVED theorem at `lean-4.32.0` + Mathlib, cloud-side** — a third-party
check that is arguably stronger than a self-hosted build. To close the local leg on a
machine with cache access: `lake exe cache get && lake build`, then re-run
`scripts/gen_registry.py` (which will flip `lake_build` to green). CI (`.github/workflows/ci.yml`)
runs this on GitHub runners where the cache is reachable.
