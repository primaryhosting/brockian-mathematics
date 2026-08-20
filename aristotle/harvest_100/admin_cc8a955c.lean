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

/-
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

/-- The shifted sum `∑ (ev i - θ)` is bounded by the sum of the eigenvalues above `θ`
(dropping the nonpositive contributions, then using `0 ≤ θ`). -/
theorem sum_sub_le_sum_above {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ) (hth : 0 ≤ theta) :
    (∑ i, ev i) - theta * d ≤
      ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), ev i := by
  classical
  set T : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hT
  have hsplit : (∑ i ∈ Finset.univ \ T, (ev i - theta)) + (∑ i ∈ T, (ev i - theta))
      = ∑ i, (ev i - theta) :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have hneg : ∑ i ∈ Finset.univ \ T, (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hnot : ¬ (theta < ev i) := by
      simp only [hT, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    linarith [not_lt.mp hnot]
  have hle : ∑ i ∈ T, (ev i - theta) ≤ ∑ i ∈ T, ev i :=
    Finset.sum_le_sum fun i _ => by linarith
  have hkey : (∑ i, ev i) - theta * d = ∑ i, (ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  rw [hkey, ← hsplit]
  linarith

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
If `0 ≤ θ` and `θ * d < ∑ ev i`, then with `n` the number of eigenvalues exceeding `θ`,
`(∑ ev i - θ * d)^2 ≤ n * ∑ (ev i)^2`. -/
theorem eigenvalue_cauchy_schwarz_count {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ)
    (hth : 0 ≤ theta) (hsum : theta * d < ∑ i, ev i) :
    ((∑ i, ev i) - theta * d) ^ 2 ≤
      ((Finset.univ.filter (fun i => theta < ev i)).card : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  set T : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hT
  have h1 : (∑ i, ev i) - theta * d ≤ ∑ i ∈ T, ev i :=
    sum_sub_le_sum_above ev theta hth
  have h0 : (0:ℝ) ≤ (∑ i, ev i) - theta * d := by linarith
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ T, ev i) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hcs : (∑ i ∈ T, ev i) ^ 2 ≤ (T.card : ℝ) * ∑ i ∈ T, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsub : ∑ i ∈ T, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => by positivity)
  calc ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ T, ev i) ^ 2 := hsq
    _ ≤ (T.card : ℝ) * ∑ i ∈ T, (ev i) ^ 2 := hcs
    _ ≤ (T.card : ℝ) * ∑ i, (ev i) ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)

end Zeta23Redux.LinAlg

