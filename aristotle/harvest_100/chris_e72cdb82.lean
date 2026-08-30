/-
# Aleph 0 Add Aleph 0
Category: Frontier — Set Theory
Target: Infinity.aleph0_add_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Infinity

/-- Cardinal arithmetic: `ℵ₀ + ℵ₀ = ℵ₀`.
Closed by Mathlib's `Cardinal.aleph0_add_aleph0`. -/
theorem aleph0_add_aleph0 :
    Cardinal.aleph0 + Cardinal.aleph0 = Cardinal.aleph0 :=
  Cardinal.aleph0_add_aleph0

/-- Cardinal arithmetic: `ℵ₀ * ℵ₀ = ℵ₀`.
Closed by Mathlib's `Cardinal.aleph0_mul_aleph0`. -/
theorem aleph0_mul_aleph0 :
    Cardinal.aleph0 * Cardinal.aleph0 = Cardinal.aleph0 :=
  Cardinal.aleph0_mul_aleph0

end Infinity

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

