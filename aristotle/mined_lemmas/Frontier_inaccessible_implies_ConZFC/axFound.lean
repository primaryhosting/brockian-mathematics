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

def axFound : setLang.Sentence :=
  ∀' ((∃' (memF (&1) (&0))) ⟹
    ∃' ((memF (&1) (&0)) ⊓ ∀' ∼((memF (&2) (&1)) ⊓ (memF (&2) (&0)))))

/-- Choice, in the form: for every set `x` of nonempty, pairwise disjoint sets there is a set
meeting each element of `x` in exactly one point. -/
