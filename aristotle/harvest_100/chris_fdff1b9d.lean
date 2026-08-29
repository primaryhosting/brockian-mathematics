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

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- The total "excess above `theta`" is at most the sum of the eigenvalues that exceed
`theta`: the indices below the threshold contribute a nonpositive amount, and subtracting
`n * theta` (with `theta ≥ 0`) only decreases the sum. -/
theorem sum_sub_le_sum_filter
    {d : ℕ} (ev : Fin d → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ i, ev i) - theta * d
      ≤ ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), ev i := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  have hsplit :
      ∑ i ∈ s, (ev i - theta) + ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i),
        (ev i - theta) = ∑ i : Fin d, (ev i - theta) := by
    rw [hs]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  have htot : ∑ i : Fin d, (ev i - theta) = (∑ i, ev i) - theta * d := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [mul_comm]
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  have hfirst : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    rw [Finset.sum_sub_distrib]
    have : (0 : ℝ) ≤ ∑ _i ∈ s, theta := Finset.sum_nonneg fun _ _ => htheta
    linarith
  linarith [hsplit, htot]

/-- Restricting the sum of squares to the above-threshold indices only decreases it. -/
theorem sum_sq_filter_le {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), (ev i) ^ 2
      ≤ ∑ i, (ev i) ^ 2 := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  positivity

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
If the eigenvalues `ev : Fin d → ℝ` have total mass exceeding `theta * d` (for a threshold
`theta ≥ 0`), and `n` is the number of eigenvalues strictly above `theta`, then
`((∑ ev) - theta * d)^2 ≤ n * ∑ (ev i)^2`. -/
theorem eigenvalue_cauchy_schwarz_count
    {d : ℕ} (ev : Fin d → ℝ) {theta : ℝ} (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hsdef : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * d < ∑ i, ev i) :
    ((∑ i, ev i) - theta * d) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  subst hsdef
  subst hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  have h1 : (∑ i, ev i) - theta * d ≤ ∑ i ∈ s, ev i :=
    sum_sub_le_sum_filter ev htheta
  have h0 : 0 ≤ (∑ i, ev i) - theta * d := by linarith
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hrest : (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 :=
    mul_le_mul_of_nonneg_left (sum_sq_filter_le ev theta) (Nat.cast_nonneg _)
  linarith

end Zeta23Redux.LinAlg

