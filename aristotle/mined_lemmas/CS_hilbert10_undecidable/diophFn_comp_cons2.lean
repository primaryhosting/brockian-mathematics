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

theorem diophFn_comp_cons2 {α : Type} {n : ℕ} {G : Vector3 ℕ (n + 2) → ℕ} (dG : DiophFn G)
    {a b : (α → ℕ) → ℕ} {w : Fin2 n → (α → ℕ) → ℕ}
    (da : DiophFn a) (db : DiophFn b) (dw : ∀ i, DiophFn (w i)) :
    DiophFn (fun v => G (Vector3.cons (a v) (Vector3.cons (b v) (fun i => w i v)))) := by
  have hall : VectorAllP DiophFn (Vector3.cons a (Vector3.cons b w)) := by
    refine (vectorAllP_iff_forall _ _).2 ?_
    intro i
    cases i with
    | fz => exact da
    | fs j =>
        cases j with
        | fz => exact db
        | fs k => exact dw k
  have h := Dioph.diophFn_comp dG (Vector3.cons a (Vector3.cons b w)) hall
  refine cast (congrArg DiophFn ?_) h
  funext v
  congr 1
  funext i
  cases i with
  | fz => rfl
  | fs j => cases j with
    | fz => rfl
    | fs k => rfl

/-! ### Primitive recursion -/

/-- Primitive recursion, in `Vector3` form. -/
