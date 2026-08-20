/-!
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 101.** The number `101` is prime — primality is spelled out
elementarily as `2 ≤ 101` together with "every divisor is `1` or `101`", so that the
statement is self-contained — and it is a sum of two squares, namely `101 = 10 ^ 2 + 1 ^ 2`.

(The same statement phrased with Mathlib's `Nat.Prime` is `Math.two_squares_101_prime`
in `RequestProject/TwoSquares101Mathlib.lean`.) -/
theorem two_squares_101 :
    (2 ≤ 101 ∧ ∀ m : Nat, m ∣ 101 → m = 1 ∨ m = 101) ∧
      ∃ a b : Nat, 101 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun m hm => ?_⟩, 10, 1, by decide⟩
  have hle : m < 102 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)
  revert hm
  revert hle
  revert m
  decide

end Math

import Mathlib
import RequestProject.TwoSquares101

/-!
# Two Squares 101, phrased with Mathlib's `Nat.Prime`
-/

namespace Math

/-- The prime `101` is a sum of two squares: `101 = 10 ^ 2 + 1 ^ 2`. -/
theorem two_squares_101_prime : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 :=
  ⟨(Nat.prime_def.2 ⟨two_squares_101.1.1, two_squares_101.1.2⟩), two_squares_101.2⟩

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

