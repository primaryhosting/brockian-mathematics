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

noncomputable def axRep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3) : setLang.Sentence :=
  Formula.iAlls (Fin n)
    (∀' ((∀' ((memF (&1) (&0)) ⟹ ∃' (φ ⊓ ∀' ((φ.liftAt 1 2) ⟹ (&3 =' &2))))) ⟹
      ∃' (∀' ((memF (&2) (&0)) ⟹ ∀' ((φ.liftAt 1 1) ⟹ (memF (&3) (&1)))))))

/-- The theory ZFC in the language of set theory. -/
