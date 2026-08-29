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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/

theorem prime_iff_dvd_factorial_succ {n : ℕ} (hn : 1 < n) :
    n.Prime ↔ n ∣ (n - 1)! + 1 := by
  have hbridge : (n ∣ (n - 1)! + 1) ↔ (((n - 1)! : ZMod n) = -1) := by
    constructor
    · intro h
      have h0 : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      push_cast at h0
      linear_combination h0
    · intro h
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [h]
      ring
  rw [hbridge, Nat.prime_iff]
  exact ⟨fun h => (Nat.prime_iff_fac_equiv_neg_one hn.ne').mp h,
    fun h => Nat.prime_of_fac_equiv_neg_one h hn.ne'⟩

/-! ## Elementary factorial facts -/

/-- `(n+1)! = 2 * (n-1)! + (n+2) * ((n-1) * (n-1)!)`, valid for `n ≥ 1`. -/
