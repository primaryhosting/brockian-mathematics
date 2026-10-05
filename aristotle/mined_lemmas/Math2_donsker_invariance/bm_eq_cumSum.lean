/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma bm_eq_cumSum {Ω' : Type*} [MeasurableSpace Ω'] {B : ℝ → Ω' → ℝ}
    (hB0 : ∀ ω, B 0 ω = 0) {u : ℕ → ℝ} (hu0 : u 0 = 0) (k : ℕ) (ω : Ω') :
    (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω)
      = cumSumCLM k fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω - B (u (j : ℕ)) ω := by
  funext j
  rw [cumSumCLM_apply, sum_fin_le_eq (fun i ↦ B (u (i + 1)) ω - B (u i) ω) j,
    Finset.sum_range_sub fun i ↦ B (u i) ω, hu0, hB0, sub_zero]

/-- **Donsker's invariance principle** (Gaussian steps): convergence of the finite-dimensional
distributions of the rescaled random walk to those of Brownian motion.

Let `X 0, X 1, …` be i.i.d. standard Gaussian random variables, `S_m = X_0 + ⋯ + X_{m-1}` and
`W_n(t) = S_{⌊nt⌋}/√n` the rescaled random walk.  Let `0 = u 0 ≤ u 1 ≤ u 2 ≤ ⋯` be times and let
`B` be a Brownian motion.  Then the random vector `(W_n(u 1), …, W_n(u k))` converges in
distribution to `(B (u 1), …, B (u k))`: for every bounded continuous `f : (Fin k → ℝ) → ℝ`,
`∫ f(W_n(u 1), …, W_n(u k)) dP → E[f(B (u 1), …, B (u k))]`. -/
