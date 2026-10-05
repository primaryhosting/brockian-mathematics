import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open scoped Classical

namespace Math2

variable {n : ℕ}

/-- A subset of `𝔽₃ⁿ` is a *cap set* if it contains no line, i.e. no three points summing to
zero other than the degenerate ones `x + x + x = 0`.  Equivalently (see
`Math2.threeAPFree_of_isCapSet`) it contains no nontrivial three-term arithmetic progression. -/

lemma threeAPFree_of_isCapSet {A : Finset (Fin n → ZMod 3)} (hA : IsCapSet A) :
    ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  intro a ha b hb c hc habc
  refine (hA a ha b hb c hc ?_).1
  have : a + b + c = a + c + b := by ring
  rw [this, habc]
  exact add_self_add_self_self b

/-- Being a cap set is exactly the same as containing no three-term arithmetic progression. -/
