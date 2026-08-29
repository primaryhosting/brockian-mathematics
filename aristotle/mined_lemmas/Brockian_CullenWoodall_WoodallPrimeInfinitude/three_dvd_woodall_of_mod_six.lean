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

lemma three_dvd_woodall_of_mod_six (k : ℕ) : 3 ∣ woodall (6 * k + 5) := by
  set n := 6 * k + 5 with hn
  have hpow : 2 ^ n % 3 = 2 := by
    have h : n = 2 * (3 * k + 2) + 1 := by omega
    rw [h]; exact two_pow_odd_mod_three _
  have hmul : n * 2 ^ n % 3 = 1 := by
    conv_lhs => rw [Nat.mul_mod, hpow]
    have h : n % 3 = 2 := by omega
    rw [h]
  have h1 : 1 ≤ n * 2 ^ n := one_le_mul_two_pow (by omega)
  have h2 := Nat.div_add_mod (n * 2 ^ n) 3
  refine ⟨n * 2 ^ n / 3, ?_⟩
  simp only [woodall]
  omega

