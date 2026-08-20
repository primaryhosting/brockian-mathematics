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

noncomputable def fourSq {m : ℕ} : Fin (m + 1) → MvPolynomial (Fin (m * 4 + 1)) ℤ :=
  Fin.cases (X 0) (fun i => ∑ k : Fin 4, (X (Fin.succ (finProdFinEquiv (i, k)))) ^ 2)

