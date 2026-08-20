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

lemma norm_add_smul_sq (w v : ℂ) (t : ℝ) :
    ‖w + (t : ℂ) * v‖ ^ 2 = ‖w‖ ^ 2 + 2 * t * (w.re * v.re + w.im * v.im) + t ^ 2 * ‖v‖ ^ 2 := by
  rw [sqnorm, sqnorm, sqnorm]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

