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

/-
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers each of
whose sum of divisors equals the sum of the two numbers plus one. -/

theorem odd_sigma_prime_pow {p e : ℕ} (hp : p.Prime) (hodd : p % 2 = 1)
    (h : Odd (sigma 1 (p ^ e))) : Even e := by
  rw [sigma_one_apply_prime_pow hp] at h
  have key : ∀ k : ℕ, (∑ j ∈ Finset.range (k + 1), p ^ j) % 2 = (k + 1) % 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have hpk : p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).pow)
        omega
  rw [Nat.odd_iff, key] at h
  rw [Nat.even_iff]
  omega

/-- If `m` is odd and `σ m` is odd, then `m` is a perfect square. -/
