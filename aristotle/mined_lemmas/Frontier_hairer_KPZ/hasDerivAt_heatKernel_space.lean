/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## Space-time partial derivatives

We work with real functions `f : ℝ → ℝ → ℝ` of a time variable and a (one dimensional)
space variable. -/

/-- Partial derivative in the time variable. -/

theorem hasDerivAt_heatKernel_space {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z : ℝ => heatKernel t z) (heatKernel t y * (-(y / (2 * t)))) y := by
  have hfun : (fun z : ℝ => heatKernel t z)
      = fun z : ℝ => Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - z ^ 2 / (4 * t)) := by
    funext z
    rw [heatKernel, if_pos ht]
  have hval : heatKernel t y
      = Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - y ^ 2 / (4 * t)) := by
    rw [heatKernel, if_pos ht]
  have htne : t ≠ 0 := ne_of_gt ht
  have hinner : HasDerivAt
      (fun z : ℝ => -(1 / 2) * Real.log (4 * Real.pi * t) - z ^ 2 / (4 * t))
      (-(y / (2 * t))) y := by
    have h1 : HasDerivAt (fun z : ℝ => z ^ 2 / (4 * t)) ((2 : ℕ) * y ^ (2 - 1) / (4 * t)) y :=
      (hasDerivAt_pow 2 y).div_const (4 * t)
    have h2 := h1.const_sub (-(1 / 2) * Real.log (4 * Real.pi * t))
    convert h2 using 1
    field_simp
    ring
  rw [hfun, hval]
  exact hinner.exp

