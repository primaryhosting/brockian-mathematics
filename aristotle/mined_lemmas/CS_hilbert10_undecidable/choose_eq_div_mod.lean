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

theorem choose_eq_div_mod (n k : ℕ) :
    n.choose k = ((2 ^ n + 1 + 1) ^ n / (2 ^ n + 1) ^ k) % (2 ^ n + 1) :=
  (choose_eq_div_mod_gen n (2 ^ n + 1) (by omega) k).symm

/-- Binomial coefficients form a Diophantine function. -/
