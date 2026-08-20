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

def DiophFnV {n : ℕ} (f : List.Vector ℕ n → ℕ) : Prop :=
  DiophFn (fun v : Vector3 ℕ n => f (toLV v))

/-! ### Primitive recursive functions are Diophantine -/

