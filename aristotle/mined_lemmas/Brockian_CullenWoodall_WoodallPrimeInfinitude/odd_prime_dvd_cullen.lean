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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem odd_prime_dvd_cullen (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  set k := p - 2 with hk
  have hpz : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hkz : ((k : ℕ) : ZMod p) = -2 := by
    have h : ((k + 2 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) := by
      congr 1
      omega
    rw [hpz] at h
    push_cast at h
    linear_combination h
  have hfer : (2 : ZMod p) ^ k * 2 = 1 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have h3 := ZMod.pow_card_sub_one_eq_one (p := p) (a := ((2 : ℕ) : ZMod p)) h2
    have hkp : k + 1 = p - 1 := by omega
    have : (2 : ZMod p) ^ (k + 1) = 1 := by
      rw [hkp]; simpa using h3
    rwa [pow_succ] at this
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [cullen]
  push_cast [hkz]
  linear_combination -hfer

end CullenWoodall
end Brockian

