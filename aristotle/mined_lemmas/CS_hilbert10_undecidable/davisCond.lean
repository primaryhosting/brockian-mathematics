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

def davisCond (p q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u K : ℕ) (a : Fin n → ℕ) : Prop :=
  davisP q v y u ∣ davisb q v y u * K + davisb q v y u + 1 ∧
    (∀ i, davisP q v y u ∣ (a i).descFactorial (u + 1)) ∧
    davisP q v y u ∣ (p (Sum.elim (Option.elim' K v) a)).natAbs

