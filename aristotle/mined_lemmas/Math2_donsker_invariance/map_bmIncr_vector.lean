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

lemma map_bmIncr_vector {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion P' B)
    {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) (k : ℕ) :
    P'.map (fun ω (j : Fin k) ↦ B (u ((j : ℕ) + 1)) ω - B (u (j : ℕ)) ω)
      = Measure.pi fun j : Fin k ↦ gaussianReal 0 (u ((j : ℕ) + 1) - u (j : ℕ)).toNNReal := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun j ↦
    ((hB.measurable _).sub (hB.measurable _)).aemeasurable).1 (hB.indep_increments k u hu hu0)]
  congr 1
  funext j
  exact hB.gaussian_increments _ _ (le_trans hu0 (hu (Nat.zero_le _))) (hu (Nat.le_succ _))

/-- The vector of values of a Brownian motion is the vector of partial sums of its increments. -/
