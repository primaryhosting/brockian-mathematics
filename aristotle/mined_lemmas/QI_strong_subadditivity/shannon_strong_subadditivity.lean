/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/

theorem shannon_strong_subadditivity (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    (∑ x, Real.negMulLog (p x)) + (∑ b, Real.negMulLog (margB p b)) ≤
      (∑ x, Real.negMulLog (margAB p x)) + (∑ y, Real.negMulLog (margBC p y)) := by
  set q : A × B × C → ℝ :=
    fun x => margAB p (x.1, x.2.1) * margBC p (x.2.1, x.2.2) / margB p x.2.1 with hq
  have hqnn : ∀ x, 0 ≤ q x := fun x =>
    div_nonneg (mul_nonneg (margAB_nonneg p hp0 _) (margBC_nonneg p hp0 _)) (margB_nonneg p hp0 _)
  have hpos : ∀ x : A × B × C, p x ≠ 0 → 0 < q x := by
    rintro ⟨a, b, c⟩ hx
    have hx0 : 0 < p (a, b, c) := lt_of_le_of_ne (hp0 _) (Ne.symm hx)
    have h1 : 0 < margAB p (a, b) := lt_of_lt_of_le hx0 (le_margAB p hp0 a b c)
    have h2 : 0 < margBC p (b, c) := lt_of_lt_of_le hx0 (le_margBC p hp0 a b c)
    have h3 : 0 < margB p b := lt_of_lt_of_le hx0 (le_margB p hp0 a b c)
    exact div_pos (mul_pos h1 h2) h3
  -- Gibbs' inequality for the subnormalised distribution `q`
  have main : 0 ≤ ∑ x, p x * Real.log (p x / q x) := by
    have h1 : ∑ x : A × B × C, (p x - q x) ≤ ∑ x, p x * Real.log (p x / q x) :=
      Finset.sum_le_sum fun x _ =>
        sub_le_mul_log_div (hp0 x) (hqnn x) fun hx => ne_of_gt (hpos x hx)
    have h2 : ∑ x : A × B × C, (p x - q x) = 1 - ∑ x, q x := by
      rw [Finset.sum_sub_distrib, hp1]
    have h3 : ∑ x, q x ≤ 1 := q_sum_le_one p hp0 hp1
    linarith
  -- expand the summand
  have expand : ∑ x : A × B × C, p x * Real.log (p x / q x)
      = ((∑ x, p x * Real.log (p x)) - (∑ x, p x * Real.log (margAB p (x.1, x.2.1)))
        - (∑ x, p x * Real.log (margBC p (x.2.1, x.2.2)))) + ∑ x, p x * Real.log (margB p x.2.1) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨a, b, c⟩ := x
    by_cases hx : p (a, b, c) = 0
    · simp [hx]
    · have hx0 : 0 < p (a, b, c) := lt_of_le_of_ne (hp0 _) (Ne.symm hx)
      have h1 : 0 < margAB p (a, b) := lt_of_lt_of_le hx0 (le_margAB p hp0 a b c)
      have h2 : 0 < margBC p (b, c) := lt_of_lt_of_le hx0 (le_margBC p hp0 a b c)
      have h3 : 0 < margB p b := lt_of_lt_of_le hx0 (le_margB p hp0 a b c)
      have hqx : q (a, b, c) = margAB p (a, b) * margBC p (b, c) / margB p b := rfl
      rw [Real.log_div hx (ne_of_gt (hpos _ hx)), hqx,
        Real.log_div (ne_of_gt (mul_pos h1 h2)) (ne_of_gt h3),
        Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
      ring
  rw [sum_p_mul_log_margAB, sum_p_mul_log_margBC, sum_p_mul_log_margB] at expand
  -- rewrite entropies
  have e1 : ∑ x, Real.negMulLog (p x) = -∑ x : A × B × C, p x * Real.log (p x) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  have e2 : ∑ y, Real.negMulLog (margAB p y)
      = -∑ y : A × B, margAB p y * Real.log (margAB p y) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  have e3 : ∑ y, Real.negMulLog (margBC p y)
      = -∑ y : B × C, margBC p y * Real.log (margBC p y) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  have e4 : ∑ b, Real.negMulLog (margB p b) = -∑ b : B, margB p b * Real.log (margB p b) := by
    simp [Real.negMulLog, Finset.sum_neg_distrib]
  rw [e1, e2, e3, e4]
  rw [expand] at main
  linarith

end Classical

section Quantum

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-! ## Partial traces of a tripartite system -/

/-- Partial trace over the first factor `A` of a tripartite system `A ⊗ B ⊗ C`. -/
