import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Real
open scoped ComplexOrder

namespace QI

/-! ## Von Neumann entropy and reduced density matrices -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a matrix, computed as the sum of
`negMulLog` over the eigenvalues.  (Defined to be `0` on non-Hermitian matrices.) -/

theorem classical_ssa_aux (p : A × B × C → ℝ) (hp : ∀ x, 0 ≤ p x)
    (pAB : A → B → ℝ) (pBC : B → C → ℝ) (pB : B → ℝ)
    (hAB : ∀ a b, pAB a b = ∑ c, p (a, b, c))
    (hBC : ∀ b c, pBC b c = ∑ a, p (a, b, c))
    (hB : ∀ b, pB b = ∑ a, ∑ c, p (a, b, c)) :
    (∑ x, Real.negMulLog (p x)) + ∑ b, Real.negMulLog (pB b)
      ≤ (∑ a, ∑ b, Real.negMulLog (pAB a b)) + ∑ b, ∑ c, Real.negMulLog (pBC b c) := by
  have hpAB : ∀ a b, 0 ≤ pAB a b := fun a b => by
    rw [hAB]; exact Finset.sum_nonneg fun c _ => hp _
  have hpBC : ∀ b c, 0 ≤ pBC b c := fun b c => by
    rw [hBC]; exact Finset.sum_nonneg fun a _ => hp _
  have hpB : ∀ b, 0 ≤ pB b := fun b => by
    rw [hB]; exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => hp _
  have hmarg1 : ∀ b, ∑ a, pAB a b = pB b := fun b => by simp [hAB, hB]
  have hmarg2 : ∀ b, ∑ c, pBC b c = pB b := fun b => by
    simp only [hBC, hB]; exact Finset.sum_comm
  have htot : ∑ b, pB b = ∑ x : A × B × C, p x := by
    rw [Fintype.sum_prod_type]
    simp only [hB]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ =>
      (Fintype.sum_prod_type (f := fun y : B × C => p (a, y))).symm
  -- the pointwise Gibbs bound
  have key : ∀ x : A × B × C, p x * (Real.log (pAB x.1 x.2.1) + Real.log (pBC x.2.1 x.2.2)
      - Real.log (pB x.2.1) - Real.log (p x))
      ≤ pAB x.1 x.2.1 * pBC x.2.1 x.2.2 / pB x.2.1 - p x := by
    rintro ⟨a, b, c⟩
    simp only
    rcases eq_or_lt_of_le (hp (a, b, c)) with h0 | h0
    · rw [← h0]
      simp only [zero_mul, sub_zero]
      exact div_nonneg (mul_nonneg (hpAB a b) (hpBC b c)) (hpB b)
    · have h1 : 0 < pAB a b := by
        rw [hAB]
        exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun c => p (a, b, c))
          (fun c _ => hp _) (Finset.mem_univ c))
      have h2 : 0 < pBC b c := by
        rw [hBC]
        exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun a => p (a, b, c))
          (fun a _ => hp _) (Finset.mem_univ a))
      have h3 : 0 < pB b := by
        rw [hB]
        refine lt_of_lt_of_le h0 ?_
        refine le_trans (Finset.single_le_sum (f := fun c => p (a, b, c))
          (fun c _ => hp _) (Finset.mem_univ c)) ?_
        exact Finset.single_le_sum (f := fun a => ∑ c, p (a, b, c))
          (fun a _ => Finset.sum_nonneg fun c _ => hp _) (Finset.mem_univ a)
      have hkey := gibbs_ineq h0 (div_pos (mul_pos h1 h2) h3)
      rw [Real.log_div (ne_of_gt (mul_pos h1 h2)) (ne_of_gt h3),
        Real.log_mul (ne_of_gt h1) (ne_of_gt h2)] at hkey
      linarith [hkey]
  -- the total mass of the comparison weight is at most that of `p`
  have hq : ∑ x : A × B × C, pAB x.1 x.2.1 * pBC x.2.1 x.2.2 / pB x.2.1 ≤ ∑ x, p x := by
    have inner : ∀ b : B, ∑ c, ∑ a, pAB a b * pBC b c / pB b ≤ pB b := by
      intro b
      have e1 : ∑ c, ∑ a, pAB a b * pBC b c / pB b = pB b * pB b / pB b := by
        have h : ∀ c : C, ∑ a, pAB a b * pBC b c / pB b = pB b * pBC b c / pB b := by
          intro c
          rw [← Finset.sum_div, ← Finset.sum_mul, hmarg1]
        rw [Finset.sum_congr rfl fun c _ => h c, ← Finset.sum_div, ← Finset.mul_sum, hmarg2]
      rw [e1]
      rcases eq_or_lt_of_le (hpB b) with h | h
      · simp [← h]
      · rw [mul_div_assoc, div_self (ne_of_gt h), mul_one]
    calc ∑ x : A × B × C, pAB x.1 x.2.1 * pBC x.2.1 x.2.2 / pB x.2.1
        = ∑ b, ∑ c, ∑ a, pAB a b * pBC b c / pB b := by
          rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
      _ ≤ ∑ b, pB b := Finset.sum_le_sum fun b _ => inner b
      _ = ∑ x, p x := htot
  -- the three marginal identities
  have E1 : ∑ x : A × B × C, p x * Real.log (pAB x.1 x.2.1)
      = ∑ a, ∑ b, pAB a b * Real.log (pAB a b) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hAB, Finset.sum_mul]
  have E2 : ∑ x : A × B × C, p x * Real.log (pBC x.2.1 x.2.2)
      = ∑ b, ∑ c, pBC b c * Real.log (pBC b c) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hBC, Finset.sum_mul]
  have E3 : ∑ x : A × B × C, p x * Real.log (pB x.2.1) = ∑ b, pB b * Real.log (pB b) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hB, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Finset.sum_mul, ← hB]
  -- putting it together
  have expand : ∑ x : A × B × C, p x * (Real.log (pAB x.1 x.2.1) + Real.log (pBC x.2.1 x.2.2)
        - Real.log (pB x.2.1) - Real.log (p x))
      = (∑ x : A × B × C, p x * Real.log (pAB x.1 x.2.1))
        + (∑ x : A × B × C, p x * Real.log (pBC x.2.1 x.2.2))
        - (∑ x : A × B × C, p x * Real.log (pB x.2.1))
        - ∑ x : A × B × C, p x * Real.log (p x) := by
    simp only [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have main : ∑ x : A × B × C, p x * (Real.log (pAB x.1 x.2.1) + Real.log (pBC x.2.1 x.2.2)
      - Real.log (pB x.2.1) - Real.log (p x)) ≤ 0 := by
    refine le_trans (Finset.sum_le_sum fun x _ => key x) ?_
    rw [Finset.sum_sub_distrib]
    linarith [hq]
  simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  linarith [E1, E2, E3, expand, main]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
/-- Strong subadditivity for the Shannon entropy of a nonnegative weight function on a
product of three finite sets. -/
