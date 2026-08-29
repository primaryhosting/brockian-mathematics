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

lemma woodall_gt_three (k : ℕ) : 3 < woodall (6 * k + 5) := by
  have h : 5 * 2 ^ 5 ≤ (6 * k + 5) * 2 ^ (6 * k + 5) := by
    have h1 : (2:ℕ) ^ 5 ≤ 2 ^ (6 * k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 5 * 2 ^ 5 ≤ 5 * 2 ^ (6 * k + 5) := Nat.mul_le_mul_left _ h1
      _ ≤ (6 * k + 5) * 2 ^ (6 * k + 5) := Nat.mul_le_mul_right _ (by omega)
  simp only [woodall]
  norm_num at h
  omega

/-- Woodall numbers with index `≡ 5 [MOD 6]` are composite, so there are infinitely many
composite Woodall numbers. -/
