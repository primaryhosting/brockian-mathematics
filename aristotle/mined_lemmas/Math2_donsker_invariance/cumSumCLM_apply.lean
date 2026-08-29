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

lemma cumSumCLM_apply {k : ℕ} (y : Fin k → ℝ) (j : Fin k) :
    cumSumCLM k y j = ∑ i : Fin k, if (i : ℕ) ≤ (j : ℕ) then y i else 0 := by
  rw [cumSumCLM]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs <;> simp

