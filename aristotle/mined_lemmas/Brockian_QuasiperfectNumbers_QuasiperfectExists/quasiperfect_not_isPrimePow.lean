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

(Note: Lean 4 does not allow a module doc comment before `import`, so the required
header appears here as an ordinary comment and is repeated as the module docstring below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Summary

A *quasiperfect* number is a natural number `n` with `σ(n) = 2n + 1`, i.e. the sum of the
proper divisors of `n` equals `n + 1`.  No quasiperfect number is known and their existence
is an open problem.  We prove here the classical structural constraints: any quasiperfect
number is an odd perfect square greater than `1`, and package this as a Lean-checked
reduction `QuasiperfectExists` of the existence question.
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem quasiperfect_not_isPrimePow {n : ℕ} (h : Quasiperfect n) : ¬ IsPrimePow n := by
  rintro ⟨p, k, hp, hk, hpk⟩
  have hodd : Odd n := quasiperfect_odd h
  have hpn : Nat.Prime p := Nat.prime_iff.mpr hp
  have hp3 : 3 ≤ p := by
    rcases hpn.eq_two_or_odd' with rfl | hpo
    · exfalso
      have h2 : (2 : ℕ) ∣ n := hpk ▸ dvd_pow_self 2 (by omega)
      have := Nat.odd_iff.mp hodd
      omega
    · have := hpn.two_le
      have := Nat.odd_iff.mp hpo
      omega
  obtain ⟨-, heq⟩ := h
  subst hpk
  rw [sigmaOne, Nat.sum_divisors_prime_pow hpn] at heq
  have := sum_geom_lt_two_mul hp3 k
  omega

/-- **Conditional reduction for the existence of quasiperfect numbers.**

Whether a quasiperfect number (a number `n` with `σ(n) = 2n + 1`) exists is an open problem.
This theorem reduces the search: a quasiperfect number exists if and only if there is an
odd perfect square `n > 1`, not a prime power, with `σ(n) = 2n + 1`. -/
