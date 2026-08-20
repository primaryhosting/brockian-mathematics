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

theorem factorial_dioph {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v)! := by
  have hr : DiophFn fun v => (f v + 1) ^ (f v + 3) :=
    Dioph.pow_dioph (Dioph.add_dioph df (Dioph.const_dioph 1))
      (Dioph.add_dioph df (Dioph.const_dioph 3))
  have hnum : DiophFn fun v => ((f v + 1) ^ (f v + 3)) ^ f v := Dioph.pow_dioph hr df
  have hmain := Dioph.div_dioph hnum (choose_dioph hr df)
  have heq : (fun v => (f v)!)
      = fun v => ((f v + 1) ^ (f v + 3)) ^ f v / ((f v + 1) ^ (f v + 3)).choose (f v) :=
    funext fun v => factorial_eq _
  rw [heq]
  exact hmain

/-- Wilson's theorem as a Diophantine-friendly characterisation of primality. -/
