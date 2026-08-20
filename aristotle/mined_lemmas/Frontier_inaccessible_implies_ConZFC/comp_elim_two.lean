import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

@[simp] theorem comp_elim_two {M : Type*} {k n : ℕ} (v : Fin k → M) (xs : Fin n → M) (i j : Fin n) :
    (Sum.elim v xs ∘ Sum.elim (fun a => Sum.inl a) (![Sum.inr i, Sum.inr j] : Fin 2 → _))
      = Sum.elim v ![xs i, xs j] := by
  funext x
  cases x with
  | inl a => simp
  | inr y => fin_cases y <;> simp

/-- Reduce the realization of a sentence in a `ZFSet`-structure to a statement about `ZFSet`s. -/
macro "realize_simp" : tactic =>
  `(tactic| ((simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_iff,
      BoundedFormula.realize_not, BoundedFormula.realize_inf, BoundedFormula.realize_sup,
      BoundedFormula.realize_bdEqual, realize_memF, Term.realize_var, Function.comp_apply,
      Sum.elim_inr, Sum.elim_inl, Fin.snoc, Formula.realize_iAlls, Formula.realize_relabel,
      BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl, id_eq,
      comp_elim_one, comp_elim_two, Unique.eq_default]); norm_num))

/-! ## Transitive sets with the right closure properties model ZFC -/

variable {A : ZFSet.{u}}

