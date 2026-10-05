/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 29.**  The number `29` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `29 = 2 ^ 2 + 5 ^ 2`.

Primality is spelled out directly (`2 ≤ 29` together with the divisor condition) rather than
via `Nat.Prime`, because the required file header (a module docstring) must be the very first
thing in the file, which precludes any `import` line; the proof is therefore self-contained. -/
theorem two_squares_29 :
    (2 ≤ 29 ∧ ∀ d : Nat, d ∣ 29 → d = 1 ∨ d = 29) ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun d hd => ?_⟩, 2, 5, by decide⟩
  have hle : d ≤ 29 := Nat.le_of_dvd (by decide) hd
  exact (by decide : ∀ d < 30, d ∣ 29 → d = 1 ∨ d = 29) d (Nat.lt_succ_of_le hle) hd

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

