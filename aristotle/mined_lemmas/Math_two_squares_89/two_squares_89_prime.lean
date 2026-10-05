/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.**  The number `89` is prime — it is at least `2` and its only
divisors are `1` and `89` — and it is a sum of two squares, namely `89 = 8 ^ 2 + 5 ^ 2`.

(The required header comment must be the first thing in the file, which rules out any
`import` line here, so primality is spelled out directly rather than via `Nat.Prime`.
The file `TwoSquares89Mathlib.lean` derives the Mathlib-flavoured statement, with
`Nat.Prime 89`, from this one.) -/

theorem two_squares_89_prime : Nat.Prime 89 ∧ ∃ a b : ℕ, 89 = a ^ 2 + b ^ 2 := by
  obtain ⟨⟨h2, hdvd⟩, hsq⟩ := two_squares_89
  exact ⟨Nat.prime_def.2 ⟨h2, hdvd⟩, hsq⟩

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

