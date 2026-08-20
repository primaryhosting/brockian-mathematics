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

theorem realize_axChoice :
    (M ⊨ axChoice) ↔ ∀ x : M,
      ((∀ z : M, memR z x → ∃ w : M, memR w z) ∧
        (∀ z : M, memR z x → ∀ z' : M, memR z' x →
          (z = z' ∨ ∀ w : M, ¬ (memR w z ∧ memR w z')))) →
      ∃ c : M, ∀ z : M, memR z x →
        ∃ w : M, (memR w z ∧ memR w c) ∧ ∀ w' : M, (memR w' z ∧ memR w' c) → w' = w := by
  simp [axChoice, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, memR]

