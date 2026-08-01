# Port Queue — keeper proofs not yet in the compiling core

Per the convergence rule (spec §4): a keeper that will not port this session is recorded
here with its blocking reason and kept OUT of the core so `lake build` stays green. Nothing
is faked. Items marked **RELEASE-BLOCKING** are §8 must-port keepers that require explicit
human sign-off to defer.

For multi-agent work, use [`docs/AGENT-COORDINATION.md`](docs/AGENT-COORDINATION.md) as
the shared queue: it records the next attackable targets, ownership suggestions, and the
explicit verification/integration contract.

## RESOLVED (re-proved fresh via the AXLE loop, 2026-07-31)

The disk originals were not recoverable (audited from Aristotle tarballs not persisted here),
so the exact ledger-admitted statements were **re-proved fresh** at Mathlib v4.32.0 via
concrete circulant/Laplacian eigenvalues and independently AXLE-verified, axiom-clean:

| Result | Ledger run | Now |
|--------|-----------|-----|
| **`golden_unique_to_five`** (φ−1 ∈ spec(C_p) ⟺ p=5) | 73 | ✅ PROVED — full biconditional, `Brockian/Spectral.lean`. The "why five" rigidity result. |
| **`pentagon_lambda2_phi`** (λ₂(C₅)=2−1/φ) | 88 | ✅ PROVED — `Brockian/Connectivity.lean`, algebraic connectivity is golden. |

## RESOLVED (2026-08-01) — full iso now proved

| Result | Ledger run | Now |
|--------|-----------|-----|
| **`Aut(C₅) ≅ D₅`** | 54 | ✅ PROVED — `Brockian.Automorphism.Full.autEquivDihedral : DihedralGroup 5 ≃* (C5 ≃g C5)`, via the `|Aut(C₅)|≤10` pinning/surjectivity argument (omega on `Fin 5`). Reverse bound closed; full isomorphism, axiom-clean. |

## PARTIAL — (superseded above; kept for history)

| Result | Ledger run | Status |
|--------|-----------|--------|
| **`Aut(C₅) ≅ D₅`** | 54 | ⬖ PARTIAL — `Brockian/Automorphism.lean` proves the faithful action `DihedralGroup 5 →* Aut(C₅)` injective, the explicit rotation/reflection automorphisms (adjacency preservation proved), and `10 ≤ |Aut(C₅)|`. **Open piece:** the reverse bound `|Aut(C₅)| ≤ 10` (which would give the full iso) — Mathlib 4.32 has no `SimpleGraph.Aut` enumeration / `Fintype (C₅ ≃g C₅)`, so it needs an explicit "an automorphism of a cycle is pinned by two adjacent images" argument. Not faked; the module claims only what it proves. |

## Ordinary port-pending (non-blocking)

| Result | Source | Reason |
|--------|--------|--------|
| ~~`singular_series_converges`~~ | SingularSeries source | **RESOLVED 2026-08-01** — proved in `Brockian.SingularSeries.Convergence` (`singularSeriesFinite_tendsto_pos`, `singular_series_pos'`); discharges `h_conv`. |
| CA-6..CA-9 (`H4_golden_ground`, `twin_lag_support`, `twin_kernel_cases`) | ConstellationAlphabet.lean | spectral-alphabet / general-prime number theory; `sorry` targets in source, out of the TransitionKernel remit. |
| `cos_5theta`, `golden_ratio_necessity`, `golden_is_geometric_invariant` | GoldenRatio.lean | Chebyshev-quintic / matrix-power arguments left as `sorry` in source. |

## Open frontier — the hard targets (attempted 2026-08-01, honestly open)

A swarm attacked Goldbach / Weyl / Riemann under strict anti-fakery discipline. None of the
open problems fell (as expected); every agent produced honest partials, no theater was found,
nothing was excluded. What genuinely verified is registered; what remains open is here.

| Target | Verified this round | Still open |
|--------|--------------------|-----------|
| **Weyl / Gate 1** | Bridge + Cayley + Chain + Kato + Gate1Bounded + **SchrodingerESA assembly** + **FreeLaplacian** / **FreeLaplacian2** (bounded + unbounded ESA transfer, discrete ξ² model) + **SchrodingerMinimal** (concrete `T` dense+symmetric) + **OperatorChoice** (bounded decaying V cannot realise large Hilbert–Pólya eigenvalues) + KatoUnbounded / Extension | **Still open:** discharge `DeficiencyRepresentsODE` for concrete `T`; continuous bounded-V ⇒ limit-point; Mathlib Plancherel L² unitary for free −Δ; full unbounded Kato range-density. |
| **Goldbach** | `goldbach_from_spectral_model` (real implication, CONDITIONAL/open), singular-series factor lemmas, small base cases (`GoldbachSchema`, `GoldbachLemmas`) | instantiating a `SpectralModel` non-trivially — that is Goldbach-strength |
| **Riemann Hypothesis** | the ξ-bridge (unconditional: `riemannXi`, Γ-nonvanishing, ξ-zero-from-ζ-zero, ξ-RH ⇒ Mathlib RH), `RH_of_BrockianSystem` (CONDITIONAL/open) (`RiemannScaffold`) | inhabiting `BrockianSystem` — a densely-defined symmetric operator with real spectrum whose eigenvalues realise the ζ-zeros. Hilbert–Pólya-strength. Not shown instantiable, and (crucially) not provably empty — so the conditional is an honest open schema, not ex-falso |

The next honest, *achievable* step is the Weyl limit-point criterion (a classical theorem, not
an open problem): closing it would unconditionally discharge Gate 1's self-adjointness clause.
It is a Mathlib-infrastructure task, not a research gamble.


## Aristotle statement-fidelity catches (2026-08-01) — the prover refuted 2 of my targets

Submitting to Aristotle v3 (proj IDs below), the untrusted prover CAUGHT REAL FLAWS in my
target statements rather than faking proofs — the methodology working end to end:

- **`boundedV_isLimitPoint` (proj 17ad1895) — REFUTED, statement was false.** "Bounded V" is
  too weak for the strong pointwise `IsSolution` (y''=(V−λ)y everywhere): the Dirichlet
  potential (0 on ℚ, 1 on ℝ∖ℚ) is bounded yet forces every classical solution ≡ 0, so no
  nontrivial solution exists and limit-point fails. Aristotle proved the counterexample and
  commented out my target. FIX for a future run: require V **continuous** (or locally
  integrable) — then bounded ⇒ limit-point is the genuine classical theorem.
- **`radius_tendsto_zero_iff` (proj 50ca67ca) — REFUTED, junk-value trap.** With `I ≡ 0`,
  Lean's `1/0 = 0` makes the radius "→0" while the mass doesn't diverge. Aristotle refuted it
  and proved the corrected `radius_tendsto_zero_iff_of_pos` (mass positive somewhere) — now
  integrated as `Brockian.Weyl.RadiusDichotomy`.

Both are now genuinely-verified NEGATIVE results + corrected positive theorems in the core.

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
