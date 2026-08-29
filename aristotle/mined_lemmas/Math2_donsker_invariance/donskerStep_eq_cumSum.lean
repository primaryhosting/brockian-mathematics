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

lemma donskerStep_eq_cumSum {X : ℕ → Ω → ℝ} {u : ℕ → ℝ} (hu : Monotone u) (hu0 : u 0 = 0)
    (n k : ℕ) (ω : Ω) :
    (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω)
      = cumSumCLM k fun j : Fin k ↦ walkIncr X u n (j : ℕ) ω := by
  set F : ℕ → ℝ := fun i ↦ ∑ x ∈ Finset.range ⌊(n : ℝ) * u i⌋₊, X x ω with hF
  have hmono : ∀ a b : ℕ, a ≤ b → ⌊(n : ℝ) * u a⌋₊ ≤ ⌊(n : ℝ) * u b⌋₊ := fun a b hab ↦
    Nat.floor_le_floor (by nlinarith [hu hab, Nat.cast_nonneg (α := ℝ) n])
  have hstep : ∀ i : ℕ, walkIncr X u n i ω = (F (i + 1) - F i) / Real.sqrt n := by
    intro i
    rw [walkIncr, hF]
    congr 1
    exact Finset.sum_Ico_eq_sub _ (hmono i (i + 1) (Nat.le_succ i))
  funext j
  rw [cumSumCLM_apply, sum_fin_le_eq (fun i ↦ walkIncr X u n i ω) j]
  simp_rw [hstep]
  rw [← Finset.sum_div, Finset.sum_range_sub F]
  have h0 : F 0 = 0 := by simp [hF, hu0]
  rw [h0, sub_zero]
  rfl

end Fdd

/-- The joint law of the increments of a Brownian motion is a product of centred Gaussians. -/
