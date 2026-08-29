/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.** The number `89` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `89 = 5 ^ 2 + 8 ^ 2`.

Primality is spelled out directly here rather than via `Nat.Prime`, because the required
file header must be the first item in the file, which prevents an `import` line.  The file
`RequestProject/TwoSquares89Prime.lean` shows that this spelling is exactly `Nat.Prime 89`. -/
theorem two_squares_89 :
    (2 ≤ 89 ∧ ∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89) ∧ ∃ a b : Nat, 89 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 5, 8, by decide⟩
  have key : ∀ m < 90, m ∣ 89 → m = 1 ∨ m = 89 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

import Mathlib
import RequestProject.TwoSquares89

/-!
# `Math.two_squares_89` in Mathlib terms

This companion file records that the hand-spelled primality condition used in
`Math.two_squares_89` is precisely `Nat.Prime 89`, and restates the result using Mathlib's
`Nat.Prime`.
-/

namespace Math

/-- The primality clause of `two_squares_89` is exactly `Nat.Prime 89`. -/
theorem prime_89_iff : (2 ≤ 89 ∧ ∀ m : ℕ, m ∣ 89 → m = 1 ∨ m = 89) ↔ Nat.Prime 89 :=
  ⟨fun h => Nat.prime_def.2 ⟨h.1, h.2⟩,
   fun h => ⟨h.two_le, fun m hm => h.eq_one_or_self_of_dvd m hm⟩⟩

/-- **Two squares for 89**, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_89_prime : Nat.Prime 89 ∧ ∃ a b : ℕ, 89 = a ^ 2 + b ^ 2 :=
  ⟨prime_89_iff.1 two_squares_89.1, two_squares_89.2⟩

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

