import Mathlib

/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**

Let `ev : Fin d → ℝ` be a list of eigenvalues and `theta ≥ 0` a threshold.  Write
`s` for the set of indices whose eigenvalue exceeds `theta` and `n = s.card`.
If `theta * d < ∑ i, ev i`, then
`(∑ i, ev i - theta * d) ^ 2 ≤ n * ∑ i, (ev i) ^ 2`.

The proof: eigenvalues below the threshold only decrease `∑ i, (ev i - theta)`,
so the left-hand base is at most `∑ i ∈ s, ev i`; then Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) on the eigenvalues above `theta`, and finally the
sum of squares over `s` is at most the sum of squares over everything. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * d < ∑ i, ev i) :
    (∑ i, ev i - theta * d) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  -- Step 1 : `∑ i, ev i - theta * d ≤ ∑ i ∈ s, ev i`.
  have hsplit : ∑ i, (ev i - theta) =
      (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ sᶜ, (ev i - theta) :=
    (Finset.sum_add_sum_compl s _).symm
  have hcompl : ∑ i ∈ sᶜ, (ev i - theta) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    have : ev i ≤ theta := by simpa [hs] using hi
    linarith
  have hs_le : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    refine Finset.sum_le_sum ?_
    intro i _
    linarith
  have htot : ∑ i, (ev i - theta) = (∑ i, ev i) - theta * d := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  have hkey : (∑ i, ev i) - theta * d ≤ ∑ i ∈ s, ev i := by
    rw [← htot, hsplit]; linarith
  -- Step 2 : square both sides (the left side is positive).
  have hpos : 0 < (∑ i, ev i) - theta * d := by linarith
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hpos) hkey
  -- Step 3 : Cauchy–Schwarz on `s`.
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- Step 4 : enlarge the sum of squares to all of `Fin d`.
  have hmono : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => sq_nonneg _)
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  calc ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := hsq
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := hcs
    _ ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hmono hcard
    _ = (n : ℝ) * ∑ i, (ev i) ^ 2 := by rw [hn]

end Zeta23Redux.LinAlg

#print axioms Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count

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

