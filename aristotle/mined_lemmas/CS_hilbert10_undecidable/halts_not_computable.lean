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

theorem halts_not_computable : ¬ ComputablePred Halts := by
  intro h
  refine ComputablePred.halting_problem 0 ?_
  obtain ⟨inst, hc⟩ := h
  refine ComputablePred.of_eq (p := fun c : Nat.Partrec.Code => Halts (Encodable.encode c))
    ⟨fun c => inst (Encodable.encode c), hc.comp Computable.encode⟩ ?_
  intro c
  simp [Halts]

/-! ### From `Poly` to `MvPolynomial` -/

/-- Every integer-valued multivariate polynomial function in the sense of `IsPoly` is the
evaluation of an honest `MvPolynomial` over `ℤ`. -/
