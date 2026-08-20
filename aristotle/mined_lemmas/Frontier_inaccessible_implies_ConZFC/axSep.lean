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

noncomputable def axSep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2) : setLang.Sentence :=
  Formula.iAlls (Fin n) (∀' ∃' ∀' ((memF (&2) (&1)) ⇔ ((memF (&2) (&0)) ⊓ φ.liftAt 1 1)))

/-- The replacement schema. For a formula `φ` whose free variables are `n` parameters together
with three bound variables, standing for the ambient set `x`, the element `z` and the value `w`,
this is the sentence
`∀ params, ∀ x, (∀ z ∈ x, ∃! w, φ) → ∃ y, ∀ z ∈ x, ∀ w, φ → w ∈ y`,
i.e. the image of `x` under the class function defined by `φ` is contained in a set. Together
with separation this gives the usual form of replacement. -/
