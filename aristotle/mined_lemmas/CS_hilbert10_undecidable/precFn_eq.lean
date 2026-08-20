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

theorem precFn_eq {n : ℕ} (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ)
    (w : Vector3 ℕ n) (x : ℕ) :
    precFn (fun v => f (toLV v)) (fun v => g (toLV v)) w x
      = Nat.rec (motive := fun _ => ℕ) (f (toLV w)) (fun y IH => g (y ::ᵥ IH ::ᵥ toLV w)) x := by
  induction x with
  | zero => rfl
  | succ y ih => simp [precFn, ih]

/-- Every primitive recursive function is Diophantine. -/
