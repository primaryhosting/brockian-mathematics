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

lemma quad_root (a b c s t : ℝ) (ha : a ≠ 0) (hs : s ^ 2 = b ^ 2 + a * c)
    (ht : t = (-b + s) / a) : 2 * t * b + t ^ 2 * a = c := by
  subst ht; field_simp; linear_combination hs

/-- If a continuous self-map of the closed unit disk (precomposed with the radial retraction)
has no fixed point, one can build a retraction of the plane onto the unit circle. -/
