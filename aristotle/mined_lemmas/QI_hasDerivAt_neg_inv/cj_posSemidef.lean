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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem cj_posSemidef (hω : ω.PosDef) {F : Mat n} (hF : F.PosSemidef) :
    (cj hω F).PosSemidef := by
  simpa [cj, Matrix.star_eq_conjTranspose] using hF.conjTranspose_mul_mul_same (eigU hω)

/-- Conversely, a matrix whose conjugate into the eigenbasis of `ω` is positive semidefinite is
itself positive semidefinite. -/
