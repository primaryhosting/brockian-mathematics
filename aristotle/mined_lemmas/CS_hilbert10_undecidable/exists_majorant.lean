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

theorem exists_majorant {γ : Type} (p : Poly γ) :
    ∃ q : Poly γ, (∀ v, 0 ≤ q v) ∧ (∀ v, |p v| ≤ q v) ∧
      ∀ v w : γ → ℕ, (∀ i, v i ≤ w i) → q v ≤ q w :=
  exists_majorant' p.isPoly

/-! ### Products of arithmetic progressions -/

/-- The product `∏_{k=1}^{y} (1 + k * b)`. -/
