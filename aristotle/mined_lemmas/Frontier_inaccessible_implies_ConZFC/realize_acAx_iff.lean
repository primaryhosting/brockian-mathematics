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

theorem realize_acAx_iff :
    M ⊨ acAx ↔ ∀ a : M, ((∀ x : M, MemR x a → ∃ z : M, MemR z x) ∧
        (∀ x y : M, ((MemR x a ∧ MemR y a) ∧ ¬x = y) → ¬∃ z : M, MemR z x ∧ MemR z y)) →
      ∃ c : M, ∀ x : M, MemR x a → ∃ z : M, (MemR z x ∧ MemR z c) ∧
        ∀ w : M, (MemR w x ∧ MemR w c) → w = z := by
  simp only [acAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, snoc10, snoc20, snoc21, snoc30,
    snoc31, snoc32, snoc41, snoc42, snoc43, snoc51, snoc52, snoc53, snoc54]

