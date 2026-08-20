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


theorem cj_cfc (hω : ω.PosDef) (f : ℝ → ℝ) :
    cj hω (cfc f ω) = Matrix.diagonal (fun i => ((f (eigV hω i) : ℝ) : ℂ)) := by
  refine conj_eq_of_spectral _ _ _ (eigU_mem hω) ?_
  rw [hω.isHermitian.cfc_eq f]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def, eigU, eigV]

