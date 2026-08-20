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

theorem dt_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dt heatKernel t x = heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hpi : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s))
      (4 * Real.pi * 1 / (4 * Real.pi * t)) t :=
    ((hasDerivAt_id t).const_mul (4 * Real.pi)).log (ne_of_gt hpi)
  have hquot : HasDerivAt (fun s : ℝ => x ^ 2 / (4 * s))
      ((0 * (4 * t) - x ^ 2 * (4 * 1)) / (4 * t) ^ 2) t :=
    (hasDerivAt_const t (x ^ 2)).div ((hasDerivAt_id t).const_mul 4) (by positivity)
  have hinner : HasDerivAt
      (fun s : ℝ => -(1 / 2) * Real.log (4 * Real.pi * s) - x ^ 2 / (4 * s))
      (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) t := by
    have h := (hlog.const_mul (-(1 / 2) : ℝ)).sub hquot
    convert h using 1
    have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hev : (fun s : ℝ => heatKernel s x) =ᶠ[nhds t]
      fun s : ℝ => Real.exp (-(1 / 2) * Real.log (4 * Real.pi * s) - x ^ 2 / (4 * s)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (0 : ℝ) from ht)] with s hs
    rw [heatKernel, if_pos (Set.mem_Ioi.mp hs)]
  have hval : heatKernel t x
      = Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - x ^ 2 / (4 * t)) := by
    rw [heatKernel, if_pos ht]
  rw [dt_apply, hev.deriv_eq, hval]
  exact hinner.exp.deriv

/-- **Base case.** The heat kernel is a positive classical solution of the linear heat equation
`∂_t Z = ∂_x² Z` on `t > 0`, i.e. of the multiplicative stochastic heat equation with zero
noise. -/
