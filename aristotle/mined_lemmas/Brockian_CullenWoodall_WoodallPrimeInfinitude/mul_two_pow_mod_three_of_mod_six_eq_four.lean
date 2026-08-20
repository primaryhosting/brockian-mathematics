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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; note `W 0 = 0`). -/

theorem mul_two_pow_mod_three_of_mod_six_eq_four {n : ℕ} (h : n % 6 = 4) :
    n * 2 ^ n % 3 = 1 := by
  have h2 : 2 ^ n = 4 ^ (n / 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [h2, Nat.mul_mod, Nat.pow_mod]
  norm_num
  omega

