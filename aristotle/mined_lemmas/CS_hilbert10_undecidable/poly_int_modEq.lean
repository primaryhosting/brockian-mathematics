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

theorem poly_int_modEq {γ : Type} (p : Poly γ) (m : ℕ) (v w : γ → ℕ)
    (h : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD (m : ℤ)]) :
    (p v : ℤ) ≡ p w [ZMOD (m : ℤ)] := by
  obtain ⟨F, hF⟩ := p
  show F v ≡ F w [ZMOD (m : ℤ)]
  induction hF with
  | proj i => exact h i
  | const n => exact Int.ModEq.refl _
  | sub _ _ ih1 ih2 => exact Int.ModEq.sub ih1 ih2
  | mul _ _ ih1 ih2 => exact Int.ModEq.mul ih1 ih2

/-- Every polynomial has a monotone, nonnegative polynomial majorant. -/
