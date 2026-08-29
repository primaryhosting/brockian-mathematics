/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

lemma sum_log_channel_le [Fintype I] [Fintype Y] (u v : I → ℝ) (M : I → Y → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (hM0 : ∀ i y, 0 ≤ M i y)
    (hM1 : ∀ i, ∑ y, M i y = 1) (hac : ∀ i, v i = 0 → u i = 0) :
    ∑ y, (∑ i, u i * M i y) * Real.log ((∑ i, u i * M i y) / (∑ i, v i * M i y))
      ≤ ∑ i, u i * Real.log (u i / v i) := by
  have key : ∀ y ∈ (univ : Finset Y),
      (∑ i, u i * M i y) * Real.log ((∑ i, u i * M i y) / (∑ i, v i * M i y))
        ≤ ∑ i, (u i * Real.log (u i / v i)) * M i y := by
    intro y _
    refine le_trans (log_sum_le (fun i => u i * M i y) (fun i => v i * M i y)
      (fun i => mul_nonneg (hu i) (hM0 i y)) (fun i => mul_nonneg (hv i) (hM0 i y)) ?_) ?_
    · intro i h
      simp only at h ⊢
      rcases mul_eq_zero.1 h with h1 | h1
      · rw [hac i h1]; ring
      · rw [h1]; ring
    · refine Finset.sum_le_sum fun i _ => le_of_eq ?_
      simp only
      rcases eq_or_lt_of_le (hM0 i y) with h0 | hpos
      · rw [← h0]; ring
      rcases eq_or_lt_of_le (hv i) with h0 | hvpos
      · rw [hac i h0.symm]; ring
      · rw [mul_div_mul_right _ _ (ne_of_gt hpos)]; ring
  refine le_trans (Finset.sum_le_sum key) (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, hM1 i, mul_one]

/-- Data-processing inequality for the mutual information: post-processing the second
component of a joint distribution through a stochastic kernel cannot increase the mutual
information. -/
