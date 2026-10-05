/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Set Real Filter Topology

/-! ### Laplace transform of `cos (a * x)` on `(0, ∞)` -/

/-- The function `x ↦ e^{-t x} cos (a x)` is integrable on `(0, ∞)` when `t > 0`. -/

theorem hasDerivAt_arctan_div (a : ℝ) (ha : 0 < a) :
    (∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => Real.arctan (t / a) / a) ((x ^ 2 + a ^ 2)⁻¹) x) ∧
      Tendsto (fun t : ℝ => Real.arctan (t / a) / a) atTop (𝓝 ((π / 2) / a)) := by
  constructor
  · intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / a) (1 / a) x := by
      simpa using (hasDerivAt_id x).div_const a
    have h3 := ((Real.hasDerivAt_arctan (x / a)).comp x h1).div_const a
    convert h3 using 1
    have hane : a ≠ 0 := ne_of_gt ha
    field_simp
    ring
  · have h0 : Tendsto (fun t : ℝ => t / a) atTop atTop :=
      Filter.Tendsto.atTop_div_const ha tendsto_id
    exact ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp h0).div_const a

