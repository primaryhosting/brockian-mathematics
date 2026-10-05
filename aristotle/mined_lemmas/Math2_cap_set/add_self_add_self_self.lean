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

lemma add_self_add_self_self (x : Fin n → ZMod 3) : x + x + x = 0 := by
  have h : ∀ a : ZMod 3, a + a + a = 0 := by decide
  funext i
  simpa using h (x i)

/-- A cap set contains no three-term arithmetic progression. -/
