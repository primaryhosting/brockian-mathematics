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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math

/-- A fixed primitive 9-th root of unity in `ℂ`. -/

lemma isPrimitiveRoot_zeta9 : IsPrimitiveRoot zeta9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

/-- The set of primitive 9-th roots of unity in `ℂ` consists of the powers `ζ ^ k`
for `k ∈ {1, 2, 4, 5, 7, 8}`, where `ζ = exp (2 π i / 9)`. -/
