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
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Cardinal

/-- The cardinality of the continuum equals `2 ^ ℵ₀`. -/
theorem continuum_eq_two_pow_aleph0 :
    Cardinal.continuum.{u} = 2 ^ Cardinal.aleph0.{u} :=
  Cardinal.two_power_aleph0.symm

/-- The cardinality of the real numbers equals `2 ^ ℵ₀`, via `Cardinal.mk_real`. -/
theorem mk_real_eq_two_pow_aleph0 :
    Cardinal.mk ℝ = 2 ^ Cardinal.aleph0.{0} :=
  Cardinal.mk_real.trans continuum_eq_two_pow_aleph0

end Cardinal

