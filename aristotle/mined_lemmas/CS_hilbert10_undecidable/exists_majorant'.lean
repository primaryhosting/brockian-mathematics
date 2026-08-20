import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem exists_majorant' {γ : Type} : ∀ {F : (γ → ℕ) → ℤ}, IsPoly F →
    ∃ q : Poly γ, (∀ v, 0 ≤ q v) ∧ (∀ v, |F v| ≤ q v) ∧
      ∀ v w : γ → ℕ, (∀ i, v i ≤ w i) → q v ≤ q w := by
  intro F hF
  induction hF with
  | proj i =>
      exact ⟨Poly.proj i, fun v => by simp, fun v => by simp, fun v w hvw => by simpa using hvw i⟩
  | const n =>
      exact ⟨Poly.const |n|, fun v => by simp, fun v => by simp, fun v w _ => le_refl _⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hp1, hm1⟩ := ih1
      obtain ⟨q2, hq2, hp2, hm2⟩ := ih2
      refine ⟨q1 + q2, fun v => by
        have := hq1 v; have := hq2 v; simp only [Poly.add_apply]; positivity,
        fun v => ?_, fun v w hvw => ?_⟩
      · simp only [Poly.add_apply]
        calc |_| ≤ |_| + |_| := abs_sub _ _
          _ ≤ q1 v + q2 v := by gcongr <;> [exact hp1 v; exact hp2 v]
      · simp only [Poly.add_apply]
        exact add_le_add (hm1 v w hvw) (hm2 v w hvw)
  | mul _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hp1, hm1⟩ := ih1
      obtain ⟨q2, hq2, hp2, hm2⟩ := ih2
      refine ⟨q1 * q2, fun v => mul_nonneg (hq1 v) (hq2 v), fun v => ?_, fun v w hvw => ?_⟩
      · simp only [Poly.mul_apply, abs_mul]
        exact mul_le_mul (hp1 v) (hp2 v) (abs_nonneg _) (hq1 v)
      · simp only [Poly.mul_apply]
        exact mul_le_mul (hm1 v w hvw) (hm2 v w hvw) (hq2 v) (le_trans (hq1 v) (hm1 v w hvw))

/-- Every polynomial has a monotone, nonnegative polynomial majorant. -/
