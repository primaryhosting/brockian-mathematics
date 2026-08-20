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

@[simp] theorem toLV_tail {n : ℕ} (v : Vector3 ℕ (n + 1)) :
    (toLV v).tail = toLV (fun i => v (Fin2.fs i)) := by
  refine List.Vector.ext fun i => ?_
  rw [List.Vector.get_tail_succ, toLV_get, toLV_get, Fin2.ofFin_succ]

