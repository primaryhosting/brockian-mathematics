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

theorem dvd_progProd {y b k : ℕ} (hk : k < y) : 1 + (k + 1) * b ∣ progProd y b :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)

