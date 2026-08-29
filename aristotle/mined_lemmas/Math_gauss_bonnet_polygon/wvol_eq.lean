import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

theorem wvol_eq {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    wvol u v = 2 / 3 * (π - angle u v) := by
  obtain ⟨e, f, he, hf, hef, hu', hv'⟩ := exists_dirv_repr hu hv
  rw [hu', hv']
  exact wvol_dirv_formula he hf hef (angle_nonneg u v) (angle_le_pi u v)

end Math

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

