import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

theorem realize_axSep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2) :
    (M ⊨ axSep φ) ↔ ∀ p : Fin n → M, ∀ x : M, ∃ y : M, ∀ z : M,
      memR z y ↔ (memR z x ∧ φ.Realize (Sum.elim default p) ![x, z]) := by
  simp [axSep, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_rel₂, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, BoundedFormula.realize_liftAt_one, memR]

