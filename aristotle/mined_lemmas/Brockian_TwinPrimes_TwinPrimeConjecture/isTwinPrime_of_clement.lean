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

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/

theorem isTwinPrime_of_clement {n : ℕ} (hn : 3 ≤ n)
    (h : n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) : IsTwinPrime n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show (k + 3) - 1 = k + 2 from rfl, show k + 3 + 2 = k + 5 from rfl] at h
  obtain ⟨j, rfl⟩ := even_of_clement h
  constructor
  · -- `2 * j + 3` is prime, by Wilson's theorem
    have hA := dvd_four_mul_of_clement h
    have hA' : (2 * j + 3) ∣ ((2 * j + 2)! + 1) :=
      (coprime_odd_four j).dvd_of_dvd_mul_left hA
    have hz : (((2 * j + 2)! + 1 : ℕ) : ZMod (2 * j + 3)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hA'
    refine (Nat.prime_iff_fac_equiv_neg_one (n := 2 * j + 3) (by omega)).mpr ?_
    rw [show (2 * j + 3) - 1 = 2 * j + 2 from rfl]
    push_cast at hz
    linear_combination hz
  · -- `2 * j + 5` is prime, by Wilson's theorem
    have hB := dvd_two_mul_of_clement h
    have hcop : Nat.Coprime (2 * j + 5) 2 := by simp [Nat.Coprime, Nat.gcd_comm]
    have hB' : (2 * j + 5) ∣ (2 * (2 * j + 2)! + 1) := hcop.dvd_of_dvd_mul_left hB
    have hz : ((2 * (2 * j + 2)! + 1 : ℕ) : ZMod (2 * j + 5)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hB'
    have h0 : ((2 * j + 5 : ℕ) : ZMod (2 * j + 5)) = 0 := ZMod.natCast_self _
    have hk4 : ((2 * j : ZMod (2 * j + 5)) + 4) = -1 := by push_cast at h0 ⊢; linear_combination h0
    have hk3 : ((2 * j : ZMod (2 * j + 5)) + 3) = -2 := by push_cast at h0 ⊢; linear_combination h0
    refine (Nat.prime_iff_fac_equiv_neg_one (n := 2 * j + 3 + 2) (by omega)).mpr ?_
    rw [show (2 * j + 3 + 2) - 1 = 2 * j + 4 from rfl,
      show 2 * j + 4 = (2 * j) + 4 from rfl, factorial_step (2 * j)]
    push_cast at hz ⊢
    rw [show ((2 : ZMod (2 * j + 3 + 2)) * j + 4) = -1 from hk4,
      show ((2 : ZMod (2 * j + 3 + 2)) * j + 3) = -2 from hk3]
    linear_combination hz

/-- **Clement's criterion**. -/
