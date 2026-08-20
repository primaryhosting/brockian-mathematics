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

theorem choose_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have hu : DiophFn fun v => 2 ^ f v + 1 :=
    Dioph.add_dioph (Dioph.pow_dioph (Dioph.const_dioph 2) df) (Dioph.const_dioph 1)
  have hnum : DiophFn fun v => (2 ^ f v + 1 + 1) ^ f v :=
    Dioph.pow_dioph (Dioph.add_dioph hu (Dioph.const_dioph 1)) df
  have hden : DiophFn fun v => (2 ^ f v + 1) ^ g v := Dioph.pow_dioph hu dg
  have hmain := Dioph.mod_dioph (Dioph.div_dioph hnum hden) hu
  have heq : (fun v => (f v).choose (g v))
      = fun v => ((2 ^ f v + 1 + 1) ^ f v / (2 ^ f v + 1) ^ g v) % (2 ^ f v + 1) :=
    funext fun v => choose_eq_div_mod _ _
  rw [heq]
  exact hmain

/-! ### Factorials -/

/-- The descending factorial `r (r-1) ⋯ (r-n+1)` is close to `r ^ n`. -/
