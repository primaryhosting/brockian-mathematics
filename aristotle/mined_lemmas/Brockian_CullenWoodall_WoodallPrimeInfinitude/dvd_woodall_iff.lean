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

lemma dvd_woodall_iff {p n : ℕ} (hn : 1 ≤ n) [Fact (Nat.Prime p)] :
    p ∣ woodall n ↔ ((n : ZMod p) * 2 ^ n = 1) := by
  have h1 : 1 ≤ n * 2 ^ n := one_le_mul_two_pow hn
  constructor
  · intro h
    have h0 : ((woodall n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have h2 : ((n * 2 ^ n : ℕ) : ZMod p) = ((woodall n : ℕ) : ZMod p) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, woodall_add_one hn]
    rw [h0, zero_add] at h2
    push_cast at h2
    exact h2
  · intro h
    have h2 : ((n * 2 ^ n : ℕ) : ZMod p) = 1 := by push_cast; exact h
    have h3 : ((woodall n : ℕ) : ZMod p) = 0 := by
      have h4 : ((woodall n + 1 : ℕ) : ZMod p) = 1 := by rw [woodall_add_one hn]; exact h2
      push_cast at h4 ⊢
      linear_combination h4
    exact (ZMod.natCast_eq_zero_iff _ _).1 h3

/-- For an odd prime `p`, `p` divides `W n` for arbitrarily large `n`.
The witness used is `n = (p-1) * ((p+1)/2 + p * N) + 1`, an element of the arithmetic
progression `n ≡ 1 [MOD p-1]`, `2n ≡ 1 [MOD p]`. -/
