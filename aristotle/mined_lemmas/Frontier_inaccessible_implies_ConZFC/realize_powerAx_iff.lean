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

theorem realize_powerAx_iff :
    M ⊨ powerAx ↔ ∀ a : M, ∃ p : M, ∀ z : M, MemR z p ↔ ∀ w : M, MemR w z → MemR w a := by
  simp only [powerAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_imp,
    BoundedFormula.realize_rel₂, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    snoc10, snoc20, snoc21, snoc30, snoc31, snoc32, snoc40, snoc42, snoc43]

