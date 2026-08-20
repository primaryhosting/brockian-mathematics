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

namespace Math

open ArithmeticFunction

/-- One of the two primitive 6-th roots of unity, `exp (π i / 3) = (1 + i √3) / 2`. -/

lemma zeta6_ne_zeta6' : zeta6 ≠ zeta6' := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  have him : zeta6.im = zeta6'.im := by rw [h]
  simp only [zeta6, zeta6'] at him
  simp at him
  linarith

/-- The primitive 6-th roots of unity in `ℂ` are exactly `(1 ± i √3) / 2`. -/
