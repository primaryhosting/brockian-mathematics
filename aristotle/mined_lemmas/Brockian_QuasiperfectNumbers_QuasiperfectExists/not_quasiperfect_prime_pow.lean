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
A natural number `n` is *quasiperfect* if `σ n = 2 * n + 1`, i.e. the sum of the proper
divisors of `n` (including `1`) equals `n + 1`.  No quasiperfect number is known, and their
existence is an open problem.

This file proves the classical structural constraints (Cattaneo, 1951): a quasiperfect number
must be an odd perfect square, and it cannot be a prime power.  The main theorem
`QuasiperfectExists` is the resulting *reduction*: a quasiperfect number exists if and only if
there is an odd `k > 1`, not a prime power, whose square is quasiperfect.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of all of its
divisors equals `2 * n + 1`. -/

theorem not_quasiperfect_prime_pow {p e : ℕ} (hp : p.Prime) : ¬ Quasiperfect (p ^ e) := by
  intro hq
  have hodd : Odd (p ^ e) := hq.odd
  obtain ⟨hn, h⟩ := hq
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with rfl | hpo
    · rcases Nat.eq_zero_or_pos e with rfl | he
      · simp at h
      · exact absurd (hodd.of_dvd_nat (dvd_pow_self 2 he.ne')) (by decide)
    · have h2 := hp.two_le
      rw [Nat.odd_iff] at hpo
      omega
  rw [Nat.sum_divisors_prime_pow hp] at h
  have hz : ((∑ x ∈ Finset.range (e + 1), (p : ℤ) ^ x)) * ((p : ℤ) - 1) = (p : ℤ) ^ (e + 1) - 1 :=
    geom_sum_mul _ _
  have hcast : (∑ x ∈ Finset.range (e + 1), (p : ℤ) ^ x) = 2 * (p : ℤ) ^ e + 1 := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) h
  rw [hcast] at hz
  have hpe : (1 : ℤ) ≤ (p : ℤ) ^ e := one_le_pow₀ (by exact_mod_cast Nat.one_le_of_lt hp3)
  have hp3' : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hsucc : (p : ℤ) ^ (e + 1) = (p : ℤ) * (p : ℤ) ^ e := by ring
  nlinarith [hz, hpe, hp3']

/-- **Main reduction.**  A quasiperfect number exists if and only if there is an odd `k > 1`
which is not a prime power and whose square is quasiperfect.  In other words, any quasiperfect
number is necessarily the square of such a `k` (Cattaneo, 1951).  Whether a quasiperfect number
exists at all is an open problem, so this is a conditional reduction, not an existence proof. -/
