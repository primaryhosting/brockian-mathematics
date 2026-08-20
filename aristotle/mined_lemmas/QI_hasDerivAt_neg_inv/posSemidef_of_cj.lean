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


theorem posSemidef_of_cj (hω : ω.PosDef) {F : Mat n} (hF : (cj hω F).PosSemidef) :
    F.PosSemidef := by
  have h1 : eigU hω * (cj hω F) * star (eigU hω) = F := by
    have hu : eigU hω * star (eigU hω) = 1 := Matrix.mem_unitaryGroup_iff.mp (eigU_mem hω)
    calc eigU hω * (star (eigU hω) * F * eigU hω) * star (eigU hω)
        = (eigU hω * star (eigU hω)) * F * (eigU hω * star (eigU hω)) := by noncomm_ring
      _ = F := by rw [hu]; simp
  rw [← h1]
  simpa [Matrix.star_eq_conjTranspose] using hF.mul_mul_conjTranspose_same (eigU hω)

