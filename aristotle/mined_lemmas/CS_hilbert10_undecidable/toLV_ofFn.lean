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

theorem toLV_ofFn {n : ℕ} (g : Fin n → ℕ) :
    toLV (fun i : Fin2 n => g (Fin2.toFin i)) = List.Vector.ofFn g := by
  refine List.Vector.ext fun i => ?_
  rw [toLV_get, List.Vector.get_ofFn, Fin2.toFin_ofFin]

/-- A function of `List.Vector`s is Diophantine if the corresponding function of `Vector3`s is. -/
