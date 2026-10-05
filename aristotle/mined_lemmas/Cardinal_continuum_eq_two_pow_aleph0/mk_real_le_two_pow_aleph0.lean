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

theorem mk_real_le_two_pow_aleph0 :
    Cardinal.mk ℝ ≤ 2 ^ Cardinal.aleph0 := by
  have h1 : Cardinal.mk ℝ ≤ Cardinal.mk (Set ℚ) :=
    Cardinal.mk_le_of_injective injective_ratsBelow
  have h2 : Cardinal.mk (Set ℚ) = 2 ^ Cardinal.mk ℚ := Cardinal.mk_set
  rw [h2, Cardinal.mk_denumerable ℚ] at h1
  exact h1

/-- Lower bound: `2 ^ ℵ₀ ≤ #ℝ`, via the Cantor function `(ℕ → Bool) ↪ ℝ`. -/
