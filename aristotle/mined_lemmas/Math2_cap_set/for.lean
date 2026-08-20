import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Filter Finset

/-- The *cap set number* `capSetNumber n` is the largest size of a subset of `𝔽₃ⁿ`
containing no non-trivial three-term arithmetic progression (a *cap set*).

Here `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`, and `ThreeAPFree` is Mathlib's predicate saying
that `a + c = b + b` with `a, b, c` in the set forces `a = b` (hence `a = b = c`). -/

theorem for finite abelian groups): the maximal size of a subset of `𝔽₃ⁿ` without non-trivial
three-term arithmetic progressions is `o(3 ^ n)`. -/
