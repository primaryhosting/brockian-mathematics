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

lemma mutualInfo_channel_le [Fintype X] [Fintype I] [Fintype Y] (r : X → I → ℝ)
    (hr : ∀ x i, 0 ≤ r x i) (M : I → Y → ℝ) (hM0 : ∀ i y, 0 ≤ M i y)
    (hM1 : ∀ i, ∑ y, M i y = 1) :
    mutualInfo (fun x y => ∑ i, r x i * M i y) ≤ mutualInfo r := by
  have hrow : ∀ x, ∑ y, (∑ i, r x i * M i y) = ∑ i, r x i := by
    intro x
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, hM1 i, mul_one]
  have hcol : ∀ y, ∑ x, (∑ i, r x i * M i y) = ∑ i, (∑ x', r x' i) * M i y := by
    intro y
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  unfold mutualInfo
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [hrow, hcol]
  have hv : ∀ y, (∑ i, r x i) * (∑ i, (∑ x', r x' i) * M i y)
      = ∑ i, ((∑ i', r x i') * (∑ x', r x' i)) * M i y := by
    intro y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hv]
  exact sum_log_channel_le (r x) (fun i => (∑ i', r x i') * (∑ x', r x' i)) M
    (fun i => hr x i)
    (fun i => mul_nonneg (Finset.sum_nonneg fun _ _ => hr x _) (Finset.sum_nonneg fun _ _ => hr _ i))
    hM0 hM1 (by
      intro i h
      rcases mul_eq_zero.1 h with h1 | h1
      · exact le_antisymm (h1 ▸ Finset.single_le_sum (f := fun i' => r x i')
          (fun i' _ => hr x i') (Finset.mem_univ i)) (hr x i)
      · exact le_antisymm (h1 ▸ Finset.single_le_sum (f := fun x' => r x' i)
          (fun x' _ => hr x' i) (Finset.mem_univ x)) (hr x i))

/-- For a joint distribution of the form `r x i = p x * q x i` with each `q x` a probability
vector, the mutual information is the entropy of the average minus the average entropy. -/
