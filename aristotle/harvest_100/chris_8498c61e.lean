/-!
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 101.**  The number `101` is prime (it is at least `2` and its only
natural divisors are `1` and itself) and it is a sum of two squares, namely
`101 = 1 ^ 2 + 10 ^ 2`.

The primality statement is spelled out from first principles rather than via `Nat.Prime`
so that this file needs no imports: Lean requires `import` commands to precede every other
piece of the file, including the mandated header comment above.  An equivalent formulation
using Mathlib's `Nat.Prime` is proved in `RequestProject.TwoSquares101Prime`. -/
theorem two_squares_101 :
    (2 ≤ 101 ∧ ∀ d, d ∣ 101 → d = 1 ∨ d = 101) ∧ ∃ a b : Nat, 101 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 1, 10, by decide⟩
  have h : ∀ d < 102, d ∣ 101 → d = 1 ∨ d = 101 := by decide
  intro d hd
  exact h d (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd)) hd

end Math

import Mathlib
import RequestProject.TwoSquares101

/-!
# Two Squares 101, Mathlib phrasing

The same result as `Math.two_squares_101`, stated with Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `101` is a sum of two squares: `101 = 1 ^ 2 + 10 ^ 2`. -/
theorem two_squares_101_prime : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 10, by norm_num⟩

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

