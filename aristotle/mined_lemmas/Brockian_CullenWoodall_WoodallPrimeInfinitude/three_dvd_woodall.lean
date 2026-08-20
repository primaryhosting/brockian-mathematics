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

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/

lemma three_dvd_woodall {n : ℕ} (hn : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  have hn1 : 1 ≤ n := by omega
  have hpow : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := two_pow_mod_three n
  have hmul : n * 2 ^ n % 3 = (n % 3) * (2 ^ n % 3) % 3 := Nat.mul_mod _ _ _
  have hW : woodall n + 1 = n * 2 ^ n := woodall_add_one hn1
  rcases hn with h | h
  · have h2 : n % 2 = 0 := by omega
    have h3 : n % 3 = 1 := by omega
    rw [if_pos h2] at hpow
    rw [hpow, h3] at hmul
    omega
  · have h3 : n % 3 = 2 := by omega
    rw [if_neg (by omega)] at hpow
    rw [hpow, h3] at hmul
    omega

/-- Woodall numbers with index `≡ 4, 5 (mod 6)` are composite (not prime). -/
