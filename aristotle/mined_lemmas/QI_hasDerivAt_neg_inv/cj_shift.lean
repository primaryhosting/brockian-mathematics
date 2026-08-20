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


theorem cj_shift (hω : ω.PosDef) (t : ℝ) :
    cj hω (ω + (t : ℂ) • 1) = Matrix.diagonal (fun i => ((eigV hω i + t : ℝ) : ℂ)) := by
  have h1 : star (eigU hω) * (eigU hω) = 1 := Matrix.mem_unitaryGroup_iff'.mp (eigU_mem hω)
  have h2 : cj hω (ω + (t : ℂ) • 1)
      = cj hω ω + (t : ℂ) • (star (eigU hω) * eigU hω) := by
    simp [cj, Matrix.mul_add, Matrix.add_mul]
  rw [h2, h1, cj_self hω]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]

