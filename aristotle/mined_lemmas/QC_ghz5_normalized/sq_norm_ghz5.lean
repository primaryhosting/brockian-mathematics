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

/-- Bitstrings of length 5, indexing the computational basis of a 5-qubit register. -/
abbrev Bits5 := Fin 5 → Fin 2

/-- The predicate picking out the two basis states `|00000⟩` and `|11111⟩`. -/

theorem sq_norm_ghz5 (b : Bits5) :
    ‖(WithLp.ofLp ghz5) b‖ ^ 2 = if AllEqual b then (1 / 2 : ℝ) else 0 := by
  unfold ghz5
  rw [WithLp.ofLp_toLp]
  split
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  · simp

/-- The 5-qubit GHZ state is a unit vector. -/
