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


theorem eigV_ge_of_sub_posSemidef (hω : ω.PosDef) {m : ℝ}
    (h : (ω - ((m : ℝ) : ℂ) • 1).PosSemidef) (i : Fin n) : m ≤ eigV hω i := by
  have hEq : ω + ((-m : ℝ) : ℂ) • 1 = ω - ((m : ℝ) : ℂ) • 1 := by
    push_cast
    module
  have hpsd : (cj hω (ω + ((-m : ℝ) : ℂ) • 1)).PosSemidef := by
    rw [hEq]
    exact cj_posSemidef hω h
  rw [cj_shift hω (-m)] at hpsd
  have hd : (0 : ℂ) ≤ Matrix.diagonal (fun i => ((eigV hω i + -m : ℝ) : ℂ)) i i :=
    hpsd.diag_nonneg
  rw [Matrix.diagonal_apply_eq] at hd
  have := (Complex.le_def.mp hd).1
  simp only [Complex.zero_re, Complex.ofReal_re] at this
  linarith

/-- Every positive definite matrix dominates a positive multiple of the identity. -/
