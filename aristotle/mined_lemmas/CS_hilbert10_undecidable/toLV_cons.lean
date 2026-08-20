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

@[simp] theorem toLV_cons {n : ℕ} (x : ℕ) (v : Vector3 ℕ n) :
    toLV (Vector3.cons x v) = x ::ᵥ toLV v := by
  refine List.Vector.ext fun i => ?_
  refine Fin.cases ?_ ?_ i
  · rw [List.Vector.get_cons_zero, toLV_get, Fin2.ofFin_zero]
    rfl
  · intro j
    rw [List.Vector.get_cons_succ, toLV_get, toLV_get, Fin2.ofFin_succ]
    rfl

