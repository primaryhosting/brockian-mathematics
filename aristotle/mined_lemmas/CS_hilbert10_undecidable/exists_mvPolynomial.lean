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

theorem exists_mvPolynomial {γ : Type} : ∀ {f : (γ → ℕ) → ℤ}, IsPoly f →
    ∃ q : MvPolynomial γ ℤ, ∀ v : γ → ℕ, f v = MvPolynomial.eval (fun i => (v i : ℤ)) q := by
  intro f hf
  induction hf with
  | proj i => exact ⟨X i, by intro v; simp⟩
  | const n => exact ⟨C n, by intro v; simp⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨q1, h1⟩ := ih1; obtain ⟨q2, h2⟩ := ih2
      exact ⟨q1 - q2, by intro v; simp [h1, h2]⟩
  | mul _ _ ih1 ih2 =>
      obtain ⟨q1, h1⟩ := ih1; obtain ⟨q2, h2⟩ := ih2
      exact ⟨q1 * q2, by intro v; simp [h1, h2]⟩

/-- A Diophantine predicate of one variable is given by an explicit integer polynomial with a
parameter: `p a` holds iff `P (a, x₁, …, xₙ) = 0` has a solution in natural numbers. -/
