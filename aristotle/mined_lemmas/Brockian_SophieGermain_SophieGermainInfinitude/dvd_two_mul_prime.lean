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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

lemma dvd_two_mul_prime {p d : ℕ} (hp : p.Prime) (hd : d ∣ 2 * p) (hnd : ¬ d ∣ p) :
    d = 2 ∨ d = 2 * p := by
  have hpos : 0 < p := hp.pos
  by_cases hpd : p ∣ d
  · right
    obtain ⟨t, rfl⟩ := hpd
    have hd' : p * t ∣ p * 2 := by rwa [mul_comm 2 p] at hd
    have ht : t ∣ 2 := (Nat.mul_dvd_mul_iff_left hpos).mp hd'
    have ht2 : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht
    interval_cases t
    · simp only [Nat.mul_zero, Nat.zero_dvd] at hd; omega
    · simp at hnd
    · exact mul_comm p 2
  · left
    have hcop : Nat.Coprime d p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
    have hd2 : d ∣ 2 := hcop.dvd_of_dvd_mul_right hd
    have h2 : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
    interval_cases d
    · simp only [Nat.zero_dvd] at hd; omega
    · exact absurd (one_dvd p) hnd
    · rfl

/-- `2 ^ n` is periodic modulo `9` with period `6`. -/
