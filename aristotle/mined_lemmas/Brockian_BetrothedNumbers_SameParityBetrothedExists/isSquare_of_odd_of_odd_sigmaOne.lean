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

lemma isSquare_of_odd_of_odd_sigmaOne : ∀ m : ℕ, Odd m → Odd (sigmaOne m) → ∃ t, m = t ^ 2 := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro hm h
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact absurd hm (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hn.ne'⟩))
      obtain ⟨j, hj⟩ := even_of_odd_sigmaOne_odd_prime_pow hp hp2 h
      exact ⟨p ^ j, by rw [hj]; ring⟩
  | zero => intro hm _; simp at hm
  | one => intro _ _; exact ⟨1, by norm_num⟩
  | coprime a b _ _ hab iha ihb =>
      intro hm h
      rw [Nat.odd_mul] at hm
      rw [sigmaOne_mul_of_coprime hab, Nat.odd_mul] at h
      obtain ⟨s, hs⟩ := iha hm.1 h.1
      obtain ⟨t, ht⟩ := ihb hm.2 h.2
      exact ⟨s * t, by rw [hs, ht]; ring⟩

/-- A positive number with odd sum of divisors is a square or twice a square. -/
