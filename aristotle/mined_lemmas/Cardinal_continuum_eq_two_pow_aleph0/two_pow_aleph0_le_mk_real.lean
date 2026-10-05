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
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Cardinal

/-- The cardinality of the continuum equals `2 ^ ℵ₀`.

In Mathlib `Cardinal.continuum` is *defined* as `2 ^ ℵ₀`, so this is the
identity witnessed by `Cardinal.two_power_aleph0`. -/

theorem two_pow_aleph0_le_mk_real :
    (2 : Cardinal) ^ Cardinal.aleph0 ≤ Cardinal.mk ℝ := by
  have hinj : Function.Injective (Cardinal.cantorFunction (1 / 3)) :=
    Cardinal.cantorFunction_injective (by norm_num) (by norm_num)
  have h1 : Cardinal.mk (ℕ → Bool) ≤ Cardinal.mk ℝ :=
    Cardinal.mk_le_of_injective hinj
  have h2 : Cardinal.mk (ℕ → Bool) = 2 ^ Cardinal.aleph0 := by
    rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
    simp
  rwa [h2] at h1

/-- The cardinality of the real numbers equals `2 ^ ℵ₀`. -/
