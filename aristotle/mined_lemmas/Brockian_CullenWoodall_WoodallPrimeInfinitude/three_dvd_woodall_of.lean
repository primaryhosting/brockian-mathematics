import Brockian.CullenWoodall

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

/-!
Mathlib (as of this toolchain) contains no material on Cullen or Woodall numbers -- a search
for `Woodall` returns nothing -- so the notions below are developed from scratch.  The Mathlib
results actually used are `strictMono_nat_of_lt_succ`, `Nat.sub_lt_sub_right`,
`Set.infinite_of_not_bddAbove` and `Set.Infinite.exists_gt`.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/

lemma three_dvd_woodall_of (k : ℕ) : 3 ∣ woodall (6 * k + 4) := by
  have hpow : 2 ^ (6 * k + 4) % 3 = 1 := by
    have h1 : (2 : ℕ) ^ (6 * k + 4) = (2 ^ 6) ^ k * 2 ^ 4 := by
      rw [pow_add, pow_mul]
    rw [h1, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hmul : (6 * k + 4) * 2 ^ (6 * k + 4) % 3 = 1 := by
    rw [Nat.mul_mod, hpow]
    omega
  have hge : 1 ≤ (6 * k + 4) * 2 ^ (6 * k + 4) := one_le_mul_two_pow (by omega)
  simp only [woodall]
  omega

