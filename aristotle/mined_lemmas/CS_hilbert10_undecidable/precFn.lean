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

def precFn {n : ℕ} (F : Vector3 ℕ n → ℕ) (G : Vector3 ℕ (n + 2) → ℕ) (w : Vector3 ℕ n) :
    ℕ → ℕ
  | 0 => F w
  | (y + 1) => G (Vector3.cons y (Vector3.cons (precFn F G w y) w))

/-- The graph of a primitive recursion is described by an existential formula, using Gödel's
β function to code the whole course of the computation. -/
