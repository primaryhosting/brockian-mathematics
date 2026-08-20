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

def davisP (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : ℕ :=
  progProd y (davisb q v y u)

/-- The three divisibility conditions of Davis' construction. -/
