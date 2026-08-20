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

@[simp] theorem toLV_get {n : ℕ} (v : Vector3 ℕ n) (i : Fin n) :
    (toLV v).get i = v (Fin2.ofFin i) := List.Vector.get_ofFn _ _

