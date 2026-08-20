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

@[simp] theorem toLV_head {n : ℕ} (v : Vector3 ℕ (n + 1)) : (toLV v).head = v Fin2.fz := by
  rw [← List.Vector.get_zero, toLV_get, Fin2.ofFin_zero]

