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

def axPow : setLang.Sentence :=
  ∀' ∃' ∀' (memF (&2) (&1) ⇔ ∀' ((memF (&3) (&2)) ⟹ (memF (&3) (&0))))

/-- Infinity: there is a set containing an empty set and closed under `y ↦ y ∪ {y}`. -/
