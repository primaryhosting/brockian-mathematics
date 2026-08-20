/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/--
The prime 17 is a sum of two squares.

Primality is spelled out elementarily (`1 < 17` and every natural divisor of `17`
is `1` or `17`), and the two-square representation is `17 = 1 ^ 2 + 4 ^ 2`.

(The required header comment must be the first thing in the file, which Lean only
permits ahead of `import` commands if there are none, so the proof is written
self-contained in core Lean rather than via `Nat.Prime` from Mathlib.)
-/
theorem two_squares_17 :
    (1 < 17 ∧ ∀ d : Nat, d ∣ 17 → d = 1 ∨ d = 17) ∧ ∃ a b : Nat, 17 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun d hd => ?_⟩, 1, 4, by decide⟩
  have hle : d ≤ 17 := Nat.le_of_dvd (by decide) hd
  have key : ∀ e : Nat, e ≤ 17 → e ∣ 17 → e = 1 ∨ e = 17 := by decide
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

