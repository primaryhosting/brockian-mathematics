import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the header block above follows `import Mathlib` because Lean 4 requires the
-- `import` commands to come first in a file.

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
If `theta ≥ 0` and the total mass `∑ ev i` exceeds `theta * d`, then the excess
`∑ ev i - theta * d` squared is bounded by `n * ∑ (ev i)^2`, where `n` is the number of
eigenvalues exceeding `theta`.  The proof drops the eigenvalues below `theta` (they only
help) and applies Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) on those above `theta`. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * (d : ℝ) < ∑ i, ev i) :
    (∑ i, ev i - theta * (d : ℝ)) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  set t : Finset (Fin d) := Finset.univ.filter (fun i => ¬ theta < ev i) with ht
  have hsplit : (∑ i ∈ s, ev i) + (∑ i ∈ t, ev i) = ∑ i, ev i := by
    rw [hs, ht]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ ev
  -- the eigenvalues below the threshold contribute at most `theta * t.card`
  have hlow : (∑ i ∈ t, ev i) ≤ theta * (t.card : ℝ) := by
    calc (∑ i ∈ t, ev i) ≤ ∑ _i ∈ t, theta := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [ht, Finset.mem_filter] at hi
          exact not_lt.mp hi.2
      _ = theta * (t.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- cardinalities add up to `d`
  have hcard : s.card + t.card = d := by
    rw [hs, ht]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin d))) (p := fun i => theta < ev i)
    simpa using this
  have hcardR : (n : ℝ) + (t.card : ℝ) = (d : ℝ) := by
    have h : ((s.card + t.card : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hcard
    push_cast at h
    rw [hn]; linarith
  -- the excess is bounded by the sum over `s`
  have hexcess : (∑ i, ev i) - theta * (d : ℝ) ≤ ∑ i ∈ s, ev i := by
    have hthetan : 0 ≤ theta * (n : ℝ) := mul_nonneg htheta (Nat.cast_nonneg n)
    have hd : theta * (d : ℝ) = theta * (n : ℝ) + theta * (t.card : ℝ) := by
      rw [← hcardR]; ring
    linarith [hsplit, hlow]
  have hpos : 0 < (∑ i, ev i) - theta * (d : ℝ) := by linarith
  have hsq : ((∑ i, ev i) - theta * (d : ℝ)) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    have h0 : 0 ≤ ∑ i ∈ s, ev i := le_trans hpos.le hexcess
    nlinarith
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmono : (∑ i ∈ s, (ev i) ^ 2) ≤ ∑ i, (ev i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => sq_nonneg (ev i))
  calc ((∑ i, ev i) - theta * (d : ℝ)) ^ 2
      ≤ (∑ i ∈ s, ev i) ^ 2 := hsq
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := hcs
    _ ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)

end Zeta23Redux.LinAlg

