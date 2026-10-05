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

def IsCapSet (A : Finset (Fin n → ZMod 3)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y ∧ y = z

