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

Two distinct positive integers `m`, `n` are *betrothed* (quasi-amicable) when the sum of the
proper divisors of each is one more than the other, i.e. `σ₁ m = σ₁ n = m + n + 1`.
All known betrothed pairs consist of one even and one odd number, and it is an open
problem whether a betrothed pair of equal parity exists.

This file proves a structural reduction for that open problem: in any same-parity betrothed
pair, each member is a perfect square or twice a perfect square (and if both members are odd,
each is a perfect square).  The main statement
`Brockian.BetrothedNumbers.SameParityBetrothedExists` records the resulting equivalence.
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma even_of_odd_sigmaOne_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (h : Odd (sigmaOne (p ^ k))) : Even k := by
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hodd
    · exact h2
  rw [sigmaOne, Nat.sum_divisors_prime_pow hp, Nat.odd_iff, Finset.sum_nat_mod] at h
  have key : ∀ i ∈ Finset.range (k + 1), p ^ i % 2 = 1 := by
    intro i _
    simp [Nat.pow_mod, hp2]
  rw [Finset.sum_congr rfl key] at h
  simp [Nat.even_iff] at h ⊢
  omega

/-- An odd number with odd sum of divisors is a perfect square. -/
