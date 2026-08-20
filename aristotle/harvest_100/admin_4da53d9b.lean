import Mathlib
import RequestProject.TwoSquares73

/-!
# Two Squares 73, in Mathlib form

This file restates `Math.two_squares_73` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`. -/
theorem two_squares_73_prime : Nat.Prime 73 ∧ ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 := by
  refine ⟨?_, two_squares_73.2⟩
  rw [Nat.prime_def_lt]
  exact ⟨two_squares_73.1.1, fun m hm hdvd => two_squares_73.1.2 m hm hdvd⟩

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
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 73.**  The number `73` is prime — it is greater than `1` and its only
divisor below itself is `1` — and it is a sum of two squares, namely `73 = 3 ^ 2 + 8 ^ 2`.

(The required header comment must be the very first thing in this file, which rules out an
`import` line here, so primality is spelled out directly instead of via `Nat.Prime`.  The file
`RequestProject.TwoSquares73Mathlib` re-derives the statement in the `Nat.Prime` form.) -/
theorem two_squares_73 :
    (1 < 73 ∧ ∀ m < 73, m ∣ 73 → m = 1) ∧ ∃ a b : Nat, 73 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, by decide⟩, 3, 8, rfl⟩

end Math

