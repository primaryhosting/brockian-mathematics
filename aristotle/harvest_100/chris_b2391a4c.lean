/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 61.**
`61` is a prime (its only divisors are `1` and `61`, and `2 ≤ 61`) and it is a sum of two
squares, namely `61 = 5 ^ 2 + 6 ^ 2`.

Note: the required header comment must be the first thing in the file, which precludes an
`import` line, so this proof is stated and proved in core Lean 4: primality is spelled out
directly as `2 ≤ 61 ∧ ∀ d, d ∣ 61 → d = 1 ∨ d = 61`, which is definitionally the usual
notion of a prime natural number. -/
theorem two_squares_61 :
    (2 ≤ 61 ∧ ∀ d : Nat, d ∣ 61 → d = 1 ∨ d = 61) ∧ ∃ a b : Nat, 61 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun d hd => ?_⟩, 5, 6, by decide⟩
  have hle : d ≤ 61 := Nat.le_of_dvd (by decide) hd
  have key : ∀ d : Nat, d ≤ 61 → d ∣ 61 → d = 1 ∨ d = 61 := by decide
  exact key d hle hd

end Math

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

