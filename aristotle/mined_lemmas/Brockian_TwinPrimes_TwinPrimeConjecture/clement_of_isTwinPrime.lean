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

theorem clement_of_isTwinPrime {n : ℕ} (hn : 3 ≤ n) (h : IsTwinPrime n) :
    n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨hp, hq⟩ := h
  have hq' : Nat.Prime (k + 5) := by simpa [show k + 3 + 2 = k + 5 from rfl] using hq
  rw [show (k + 3) - 1 = k + 2 from rfl]
  -- oddness of `k + 3`
  have hodd : ¬ (2 ∣ (k + 3)) := by
    intro h2
    have : (2 : ℕ) ∣ k + 5 := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hq' 2 this)
    omega
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  subst hj
  -- divisibility by `k + 3`
  have hdvd1 : (2 * j + 3) ∣ 4 * ((2 * j + 2)! + 1) + (2 * j + 3) := by
    have hw := (Nat.prime_iff_fac_equiv_neg_one (n := 2 * j + 3) (by omega)).mp hp
    rw [show (2 * j + 3) - 1 = 2 * j + 2 from rfl] at hw
    have hz : (((2 * j + 2)! + 1 : ℕ) : ZMod (2 * j + 3)) = 0 := by push_cast [hw]; ring
    have : (2 * j + 3) ∣ ((2 * j + 2)! + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact Dvd.dvd.add (this.mul_left 4) dvd_rfl
  -- divisibility by `k + 5`
  have hdvd2 : (2 * j + 5) ∣ 4 * ((2 * j + 2)! + 1) + (2 * j + 3) := by
    have h2 := two_factorial_eq (2 * j) hq'
    have hz : ((4 * ((2 * j + 2)! + 1) + (2 * j + 3) : ℕ) : ZMod (2 * j + 5)) = 0 := by
      have h0 : ((2 * j + 5 : ℕ) : ZMod (2 * j + 5)) = 0 := ZMod.natCast_self _
      push_cast at h2 h0 ⊢
      linear_combination 2 * h2 + h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_shift_two j) hdvd1 hdvd2
  simpa [show 2 * j + 3 + 2 = 2 * j + 5 from rfl] using this

/-- From Clement's divisibility one gets `(k + 5) ∣ 2 * (2 * (k + 2)! + 1)`. -/
