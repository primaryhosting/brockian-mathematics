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

namespace QC

/-- The primitive `16`-th root of unity `exp(2πi/16)` used for the 4-qubit QFT. -/

lemma omega16_pow_inj {j k : ℕ} (hj : j < 16) (hk : k < 16)
    (h : omega16 ^ j = omega16 ^ k) : j = k :=
  isPrimitiveRoot_omega16.pow_inj hj hk h

/-- **The 4-qubit QFT matrix is unitary.** -/
