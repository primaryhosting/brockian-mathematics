import Brockian.RieselCovering

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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is composite
(equivalently, not prime, since these numbers are `> 1`) for every `n ≥ 1`. -/

theorem dvd_of_period {p k r n : ℕ} (hk : 1 ≤ k) (h24 : p ∣ 2 ^ 24 - 1)
    (hr : p ∣ k * 2 ^ r - 1) (hn : n % 24 = r) : p ∣ k * 2 ^ n - 1 := by
  have hkr : 1 ≤ k * 2 ^ r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by positivity))
  have hkn : 1 ≤ k * 2 ^ n := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by positivity))
  have h1 : (1 : ℕ) ≡ 2 ^ 24 [MOD p] := (Nat.modEq_iff_dvd' (by norm_num)).mpr h24
  have h2 : (1 : ℕ) ≡ k * 2 ^ r [MOD p] := (Nat.modEq_iff_dvd' hkr).mpr hr
  have h3 : 2 ^ r ≡ 2 ^ n [MOD p] := by
    conv_rhs => rw [← Nat.div_add_mod n 24, hn]
    rw [pow_add, pow_mul]
    calc (2 : ℕ) ^ r = 1 ^ (n / 24) * 2 ^ r := by ring
      _ ≡ (2 ^ 24) ^ (n / 24) * 2 ^ r [MOD p] := Nat.ModEq.mul (h1.pow _) (Nat.ModEq.refl _)
  have h4 : (1 : ℕ) ≡ k * 2 ^ n [MOD p] := h2.trans (Nat.ModEq.mul (Nat.ModEq.refl k) h3)
  exact (Nat.modEq_iff_dvd' hkn).mp h4

/-- The covering system for `k = 509203`: for every residue `r < 24`, one of the primes
`3, 5, 7, 13, 17, 241` divides `509203 * 2 ^ r - 1`. -/
