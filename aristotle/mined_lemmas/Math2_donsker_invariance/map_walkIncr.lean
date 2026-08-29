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

lemma map_walkIncr {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (u : ℕ → ℝ) (n j : ℕ) :
    P.map (walkIncr X u n j) = gaussianReal 0 (walkIncrVar u n j) := by
  have hcomp : walkIncr X u n j = (fun x ↦ (Real.sqrt n)⁻¹ * x) ∘
      fun ω ↦ ∑ i ∈ Finset.Ico ⌊(n : ℝ) * u j⌋₊ ⌊(n : ℝ) * u (j + 1)⌋₊, X i ω := by
    funext ω; simp [walkIncr, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), map_finsetSum hmeas hindep hlaw,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    have h1 : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rw [walkIncrVar, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), h1,
      Nat.card_Ico]
    ring

/-- The increments of the rescaled walk over disjoint time intervals are independent. -/
