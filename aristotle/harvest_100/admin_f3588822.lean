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

namespace Zeta23Redux.LinAlg

open Finset

/-- **Thresholded Cauchy–Schwarz count** (Lemma 3.3, eigenvalue level).

For eigenvalues `ev : Fin d → ℝ` and a threshold `theta ≥ 0`, if the total sum of eigenvalues
exceeds `theta * d`, then the excess `(∑ ev) - theta * d` satisfies
`((∑ ev) - theta * d) ^ 2 ≤ n * ∑ (ev i) ^ 2`, where `n` is the number of eigenvalues above
`theta`.  The proof drops the eigenvalues below `theta` (they only decrease the excess) and then
applies Cauchy–Schwarz to the eigenvalues above `theta`. -/
theorem eigenvalue_cauchy_schwarz_count {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ)
    (htheta : 0 ≤ theta)
    (hsum : theta * d < ∑ i, ev i) :
    (∑ i, ev i - theta * d) ^ 2
      ≤ (((univ.filter (fun i => theta < ev i)).card : ℕ) : ℝ) * ∑ i, (ev i) ^ 2 := by
  set s : Finset (Fin d) := univ.filter (fun i => theta < ev i) with hs
  -- the excess equals the sum of the shifted eigenvalues
  have hshift : ∑ i, (ev i - theta) = ∑ i, ev i - theta * d := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- dropping the eigenvalues at or below `theta` only increases the shifted sum
  have hsplit : ∑ i, (ev i - theta)
      = (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ univ.filter (fun i => ¬ theta < ev i), (ev i - theta) := by
    rw [hs, Finset.sum_filter_add_sum_filter_not]
  have hneg : ∑ i ∈ univ.filter (fun i => ¬ theta < ev i), (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  have hle1 : ∑ i, ev i - theta * d ≤ ∑ i ∈ s, (ev i - theta) := by
    rw [← hshift, hsplit]; linarith
  have hle2 : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    apply Finset.sum_le_sum
    intro i _
    linarith
  have hpos : 0 < ∑ i, ev i - theta * d := by linarith
  have hkey : ∑ i, ev i - theta * d ≤ ∑ i ∈ s, ev i := le_trans hle1 hle2
  have hsq : (∑ i, ev i - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    apply sq_le_sq' <;> nlinarith
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmono : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  calc (∑ i, ev i - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := hsq
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := hcs
    _ ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hmono hcard

end Zeta23Redux.LinAlg

