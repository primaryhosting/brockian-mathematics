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

theorem hilbert10_undecidable :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ => ∃ x : Fin n → ℕ,
          MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) P = 0 := by
  obtain ⟨n, P, hP⟩ := exists_poly_of_dioph Halts (dioph_of_rePred Halts halts_re)
  refine ⟨n, P, fun h => halts_not_computable (ComputablePred.of_eq h ?_)⟩
  intro a
  exact hP a

/-! ### Solutions in the integers -/

/-- The substitution replacing each unknown by a sum of four squares of new unknowns, and
leaving the parameter untouched. -/
