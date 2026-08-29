import Brockian.LandauNSquaredPlusOne

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

namespace Brockian.LandauNSquaredPlusOne

open Set

/-- The set of primes of the form `n ^ 2 + 1` (the "Landau primes"). -/

theorem mod_four_eq_one_of_prime_dvd_sq_add_one {p n : ℕ} (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne3 : p % 4 ≠ 3 := by
    have : ((n : ZMod p)) ^ 2 = -1 := by
      have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      push_cast at h0
      linear_combination h0
    rw [← ZMod.exists_sq_eq_neg_one_iff]
    exact ⟨(n : ZMod p), by rw [← this]; ring⟩
  have h2 : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hodd)
  omega

/-- Unconditionally, infinitely many primes divide some value of `n ^ 2 + 1`. -/
