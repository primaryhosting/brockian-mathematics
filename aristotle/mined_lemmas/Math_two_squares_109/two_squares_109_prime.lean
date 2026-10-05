import Mathlib
import RequestProject.TwoSquares109

/-!
# Two Squares 109 (Mathlib phrasing)

Restatements of `Math.two_squares_109` using Mathlib's `Nat.Prime`, together with
the check that the elementary primality condition used in `Math.two_squares_109`
is exactly `Nat.Prime 109`.
-/

namespace Math

/-- The elementary primality condition appearing in `Math.two_squares_109`
(`2 ≤ n` and every divisor of `n` is `1` or `n`) is equivalent to `Nat.Prime n`. -/

theorem two_squares_109_prime : Nat.Prime 109 ∧ ∃ a b : ℕ, 109 = a ^ 2 + b ^ 2 :=
  ⟨(nat_prime_iff_elementary 109).2 two_squares_109.1, two_squares_109.2⟩

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

/-!
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 109 is a sum of two squares.**

Primality is stated in elementary terms (`2 ≤ 109`, and every divisor of `109`
is either `1` or `109`), and the representation is `109 = 10² + 3²`.

The divisor condition is reduced to a finite check: any divisor of the positive
number `109` is at most `109`, so it suffices to inspect the finitely many
candidates below `110`. -/
