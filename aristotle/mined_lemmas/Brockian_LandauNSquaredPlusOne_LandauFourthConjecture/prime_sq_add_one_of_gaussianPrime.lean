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

open Zsqrtd

/-- A *Landau prime* is a prime natural number of the form `n ^ 2 + 1`. -/

lemma prime_sq_add_one_of_gaussianPrime {n : ℕ} (h : Prime (⟨(n : ℤ), 1⟩ : GaussianInt)) :
    Nat.Prime (n ^ 2 + 1) := by
  set x : GaussianInt := ⟨(n : ℤ), 1⟩ with hx
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h.not_unit (norm_eq_one_iff.1 (by simp [hx, Zsqrtd.norm]))
  have hxdvd : x ∣ ((n ^ 2 + 1 : ℕ) : GaussianInt) := by
    refine ⟨star x, ?_⟩
    have h1 : ((x.norm : ℤ) : GaussianInt) = x * star x := Zsqrtd.norm_eq_mul_conj x
    rw [← h1, hx, norm_mk_one n]
    push_cast
    ring
  obtain ⟨p, hp, hpm, hxp⟩ :=
    exists_natPrime_dvd_of_dvd_natCast h (m := n ^ 2 + 1) (by positivity) hxdvd
  have hnormdvd : ((n ^ 2 + 1 : ℕ) : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
    obtain ⟨y, hy⟩ := hxp
    refine ⟨y.norm, ?_⟩
    have hcongr := congrArg Zsqrtd.norm hy
    rw [Zsqrtd.norm_mul, hx, norm_mk_one n] at hcongr
    push_cast at hcongr ⊢
    simpa [Zsqrtd.norm, sq] using hcongr
  have hnormdvd' : (n ^ 2 + 1) ∣ p ^ 2 := by exact_mod_cast hnormdvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).1 hnormdvd'
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases k
  · exfalso
    rw [pow_zero] at hkeq
    nlinarith
  · rw [pow_one] at hkeq
    rw [hkeq]
    exact hp
  · exfalso
    have hlt : n < p := by nlinarith
    nlinarith

/-- **Equivalence**: `n + i` is a Gaussian prime iff `n ^ 2 + 1` is a rational prime. -/
