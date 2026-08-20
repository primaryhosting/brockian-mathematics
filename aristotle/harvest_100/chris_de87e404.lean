import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 (Mathlib formulation)

The same result as `Math.two_squares_5`, but with primality stated via `Nat.Prime`.
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/
theorem two_squares_5_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 2, by norm_num⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for the prime 5.**

`5` is prime (it is at least `2` and its only divisors are `1` and `5`) and it is a sum of
two squares, namely `5 = 1 ^ 2 + 2 ^ 2`.

The primality is spelled out elementarily (rather than via `Nat.Prime`) so that the file can
start with the required header comment, which must precede any `import`. An equivalent
statement using Mathlib's `Nat.Prime` is proved in `RequestProject.TwoSquares5Mathlib`. -/
theorem two_squares_5 :
    (2 ≤ 5 ∧ ∀ m : Nat, m ∣ 5 → m = 1 ∨ m = 5) ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 2, by decide⟩
  have key : ∀ m : Nat, m < 6 → m ∣ 5 → m = 1 ∨ m = 5 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

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

