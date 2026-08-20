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

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite number `n > 1` such that `p ∣ n / p - 1` for every
prime `p` dividing `n`. -/

lemma prod_dvd_numerator_iff (hS : ∀ p ∈ S, p.Prime) :
    ((∏ p ∈ S, p : ℕ) : ℤ) ∣ ((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1) ↔
      ∀ p ∈ S, (p : ℤ) ∣ ((∏ r ∈ S.erase p, (r : ℤ)) - 1) := by
  classical
  constructor
  · intro h p hp
    refine (dvd_numerator_iff hp).mp (dvd_trans ?_ h)
    exact_mod_cast Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ hp)
  · intro h
    rw [Nat.cast_prod]
    refine Finset.prod_dvd_of_coprime ?_ fun p hp => (dvd_numerator_iff hp).mpr (h p hp)
    intro p hp q hq hne
    simp only [Function.onFun]
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hne)

/-- Giuga's expression written as a single fraction. -/
