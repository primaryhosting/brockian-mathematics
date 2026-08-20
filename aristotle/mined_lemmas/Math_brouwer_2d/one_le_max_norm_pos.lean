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

namespace BrouwerAux

/-- The radial retraction of the plane `ℂ` onto the closed unit disk. -/

lemma one_le_max_norm_pos (z : ℂ) : (0:ℝ) < max 1 ‖z‖ :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

