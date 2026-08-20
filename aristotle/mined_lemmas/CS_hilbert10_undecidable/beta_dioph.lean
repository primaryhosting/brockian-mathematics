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

theorem beta_dioph {α : Type} {c d i : (α → ℕ) → ℕ} (dc : DiophFn c) (dd : DiophFn d)
    (di : DiophFn i) : DiophFn fun v => beta (c v) (d v) (i v) :=
  Dioph.mod_dioph dc (Dioph.add_dioph (Dioph.const_dioph 1)
    (Dioph.mul_dioph (Dioph.add_dioph di (Dioph.const_dioph 1)) dd))

/-! ### Composition -/

/-- Composition of a Diophantine function of `n+2` arguments with Diophantine functions. -/
