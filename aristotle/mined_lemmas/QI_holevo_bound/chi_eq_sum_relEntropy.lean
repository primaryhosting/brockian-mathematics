import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma chi_eq_sum_relEntropy {ι Z : Type*} [Fintype ι] [Fintype Z]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (r : ι → Z → ℝ) (hr0 : ∀ i z, 0 ≤ r i z)
    (rbar : Z → ℝ) (hrb : ∀ z, rbar z = ∑ j, p j * r j z) :
    ∑ i, p i * relEntropy (r i) rbar
      = shannonEntropy rbar - ∑ i, p i * shannonEntropy (r i) := by
  have hsplit : ∀ i, p i * relEntropy (r i) rbar
      = p i * (∑ z, r i z * Real.log (r i z)) - p i * (∑ z, r i z * Real.log (rbar z)) := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · rw [← hpi]; ring
    · have hre : relEntropy (r i) rbar
          = (∑ z, r i z * Real.log (r i z)) - (∑ z, r i z * Real.log (rbar z)) := by
        rw [relEntropy, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro z _
        rcases eq_or_lt_of_le (hr0 i z) with hz | hz
        · rw [← hz]; ring
        · have hrb' : 0 < rbar z := by
            rw [hrb z]
            refine lt_of_lt_of_le (mul_pos hpi hz) ?_
            exact Finset.single_le_sum (f := fun j => p j * r j z)
              (fun j _ => mul_nonneg (hp0 j) (hr0 j z)) (Finset.mem_univ i)
          rw [Real.log_div (ne_of_gt hz) (ne_of_gt hrb')]
          ring
      rw [hre]; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsplit i), Finset.sum_sub_distrib]
  have h1 : ∑ i, p i * (∑ z, r i z * Real.log (r i z)) = -∑ i, p i * shannonEntropy (r i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [shannonEntropy_eq_neg_sum]
    ring
  have h2 : ∑ i, p i * (∑ z, r i z * Real.log (rbar z)) = -shannonEntropy rbar := by
    have hcomm : ∑ i, p i * (∑ z, r i z * Real.log (rbar z))
        = ∑ z, rbar z * Real.log (rbar z) := by
      simp only [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro z _
      rw [← Finset.sum_mul, ← hrb z]
    rw [hcomm, shannonEntropy_eq_neg_sum, neg_neg]
  rw [h1, h2]
  ring

/-- **Classical Holevo bound**: for an ensemble of probability vectors `r i` with prior `p`,
and any classical channel `E`, the mutual information between the label and the outcome is at
most the Holevo quantity `H(∑ p i r i) - ∑ p i H(r i)`. -/
