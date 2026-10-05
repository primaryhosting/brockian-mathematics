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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime.
Landau's fourth problem asserts that this set is infinite; it is open. -/

theorem prime_of_no_small_prime_factor {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ≤ n → ¬ p ∣ n ^ 2 + 1) : Nat.Prime (n ^ 2 + 1) := by
  by_contra hc
  have hpos : 0 < n ^ 2 + 1 := Nat.succ_pos _
  have hne1 : n ^ 2 + 1 ≠ 1 := by
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    omega
  have hprime : Nat.Prime (n ^ 2 + 1).minFac := Nat.minFac_prime hne1
  have hsq : (n ^ 2 + 1).minFac ^ 2 ≤ n ^ 2 + 1 := Nat.minFac_sq_le_self hpos hc
  have hle : (n ^ 2 + 1).minFac ≤ n := by
    by_contra hgt
    push_neg at hgt
    have h2 : (n + 1) ^ 2 ≤ (n ^ 2 + 1).minFac ^ 2 := Nat.pow_le_pow_left hgt 2
    nlinarith [hsq, h2]
  exact h _ hprime hle (Nat.minFac_dvd _)

/-- Conversely, if `n ^ 2 + 1` is prime then no prime `p ≤ n` divides it. -/
