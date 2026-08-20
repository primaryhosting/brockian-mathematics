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


theorem classical_path_identity {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Ioo (0:ℝ) 1, (1 - s) * (p - q) ^ 2 / (q + s * (p - q))
      = p * Real.log p - p * Real.log q - p + q := by
  have hderiv : ∀ s ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => p * Real.log (q + s * (p - q)) - (q + s * (p - q)))
        ((1 - s) * (p - q) ^ 2 / (q + s * (p - q))) s := by
    intro s hs
    have hne : q + s * (p - q) ≠ 0 := ne_of_gt (pos_path hp hq hs)
    have h1 : HasDerivAt (fun s : ℝ => q + s * (p - q)) (p - q) s := by
      simpa using ((hasDerivAt_id s).mul_const (p - q)).const_add q
    have h3 := ((h1.log hne).const_mul p).sub h1
    convert h3 using 1
    field_simp
    ring
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_classical_path hp hq).intervalIntegrable
  rw [intervalIntegral.integral_of_le (by norm_num)] at key
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo] at key
  rw [key]
  simp
  ring

/-- Integrability of the classical path integrand. -/
