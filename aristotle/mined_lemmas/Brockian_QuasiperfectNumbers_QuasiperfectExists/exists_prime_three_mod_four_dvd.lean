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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quasiperfect numbers

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper
divisors is `n + 1`.  No quasiperfect number is known, and their existence is a
long-standing open problem.

This file proves Cattaneo's theorem — every quasiperfect number is an odd perfect
square — and deduces from it the conditional reduction
`Brockian.QuasiperfectNumbers.QuasiperfectExists`: a quasiperfect number exists if and
only if a quasiperfect number that is an odd perfect square exists.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- `sigmaSum n` is the sum of all positive divisors of `n`. -/

theorem exists_prime_three_mod_four_dvd :
    ∀ m : ℕ, m % 4 = 3 → ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    by_cases h3 : p % 4 = 3
    · exact ⟨p, hp, h3, hpd⟩
    · obtain ⟨k, hk⟩ := hpd
      have hp2 : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · subst h; omega
        · exact h
      have hp4 : p % 4 = 1 := by omega
      have hk4 : k % 4 = 3 := by
        have : m % 4 = (p % 4) * (k % 4) % 4 := by rw [hk, Nat.mul_mod]
        rw [hp4] at this; omega
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; omega
        · exact h
      have hklt : k < m := by
        rw [hk]; exact (Nat.lt_mul_iff_one_lt_left hk0).mpr hp.one_lt
      obtain ⟨q, hq, hq3, hqd⟩ := ih k hklt hk4
      exact ⟨q, hq, hq3, hqd.trans ⟨p, by rw [hk]; ring⟩⟩

/-- No prime `p ≡ 3 (mod 4)` divides `y ^ 2 + 1`. -/
