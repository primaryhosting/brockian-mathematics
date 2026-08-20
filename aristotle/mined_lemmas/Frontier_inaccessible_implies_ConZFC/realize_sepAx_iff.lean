/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes the statement that a (strongly) inaccessible cardinal `κ` yields a model of
`ZFC`, namely the rank-initial segment `V κ = {x : ZFSet | rank x < κ.ord}` of the von Neumann
hierarchy, and deduces the semantic consistency statement `Con(ZFC)` (i.e. satisfiability of the
first-order theory `ZFCTheory`) from the existence of an inaccessible cardinal.
-/

universe u

namespace Frontier

open FirstOrder Language Cardinal Ordinal ZFSet

/-! ## The first-order language of set theory -/

/-- The relations of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of set theory: one binary relation symbol, no functions. -/

theorem realize_sepAx_iff (φ : setLang.BoundedFormula Empty (n + 1)) :
    M ⊨ sepAx φ ↔ ∀ (xs : Fin n → M) (a : M), ∃ b : M, ∀ x : M,
      MemR x b ↔ (MemR x a ∧ φ.Realize default (Fin.snoc xs x)) := by
  simp only [sepAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_inf,
    BoundedFormula.realize_rel₂, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    Fin.snoc_last, Fin.snoc_castSucc,
    BoundedFormula.realize_liftAt (show n + 2 ≤ (n + 1) + 1 by omega), val_lemma1]

