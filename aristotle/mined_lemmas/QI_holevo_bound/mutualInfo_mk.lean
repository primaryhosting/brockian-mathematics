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

lemma mutualInfo_mk [Fintype X] [Fintype I] (p : X → ℝ) (q : X → I → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq0 : ∀ x i, 0 ≤ q x i) (hq1 : ∀ x, ∑ i, q x i = 1) :
    mutualInfo (fun x i => p x * q x i)
      = shannonEntropy (fun i => ∑ x, p x * q x i) - ∑ x, p x * shannonEntropy (q x) := by
  have hmarg1 : ∀ x, ∑ i', p x * q x i' = p x := fun x => by rw [← Finset.mul_sum, hq1 x, mul_one]
  have term : ∀ x i, (p x * q x i) * Real.log ((p x * q x i) / (p x * ∑ x', p x' * q x' i))
      = p x * (q x i * Real.log (q x i))
        - (p x * q x i) * Real.log (∑ x', p x' * q x' i) := by
    intro x i
    rcases eq_or_lt_of_le (hp x) with h0 | hppos
    · rw [← h0]; ring
    rcases eq_or_lt_of_le (hq0 x i) with h0 | hqpos
    · rw [← h0]; simp
    have hqb0 : 0 < ∑ x', p x' * q x' i := lt_of_lt_of_le (mul_pos hppos hqpos)
      (Finset.single_le_sum (f := fun x' => p x' * q x' i)
        (fun x' _ => mul_nonneg (hp x') (hq0 x' i)) (Finset.mem_univ x))
    rw [mul_div_mul_left _ _ (ne_of_gt hppos), Real.log_div (ne_of_gt hqpos) (ne_of_gt hqb0)]
    ring
  unfold mutualInfo shannonEntropy
  simp only [hmarg1, term]
  have hA : ∀ x, ∑ i, (p x * (q x i * Real.log (q x i))
        - (p x * q x i) * Real.log (∑ x', p x' * q x' i))
      = p x * (∑ i, q x i * Real.log (q x i))
        - ∑ i, (p x * q x i) * Real.log (∑ x', p x' * q x' i) := by
    intro x; rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [hA]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have h1 : ∀ x, p x * (∑ i, q x i * Real.log (q x i)) = - (p x * ∑ i, Real.negMulLog (q x i)) := by
    intro x
    simp [Real.negMulLog, Finset.mul_sum]
  have h2 : ∑ i, ∑ x, (p x * q x i) * Real.log (∑ x', p x' * q x' i)
      = - ∑ i, Real.negMulLog (∑ x, p x * q x i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    simp [Real.negMulLog]
  rw [h2]
  simp only [h1]
  rw [Finset.sum_neg_distrib]
  ring

/-! ## Quantum states, measurements and entropies -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix: positive semidefinite with unit trace. -/
