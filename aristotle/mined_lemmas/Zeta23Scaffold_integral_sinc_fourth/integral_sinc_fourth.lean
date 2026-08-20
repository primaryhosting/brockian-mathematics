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

The header above is repeated as a plain comment on the first line of this file, since Lean 4
requires `import` commands to precede any module docstring.

## Method

With `T u = max 0 (1 - |u|)` the tent function, an explicit computation gives
`𝓕 T ξ = sinc (π ξ) ^ 2`.  The convolution theorem then yields `𝓕 (T ⋆ T) ξ = sinc (π ξ) ^ 4`,
and Fourier inversion at `0` gives
`∫ sinc (π ξ) ^ 4 dξ = (T ⋆ T) 0 = ∫ T ² = 2/3`.
Rescaling by `π` produces `∫ (sin x / x) ^ 4 dx = 2π/3`.
-/

open MeasureTheory Convolution FourierTransform
open scoped Real

namespace Zeta23Scaffold

/-- The tent (triangle) function `u ↦ max 0 (1 - |u|)`. -/

theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * π / 3 := by
  have h1 : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = |π⁻¹| • ∫ x : ℝ, Real.sinc x ^ 4 :=
    Measure.integral_comp_mul_left (fun x => Real.sinc x ^ 4) π
  rw [integral_sinc_pi_fourth, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at h1
  have h2 : ∫ x : ℝ, Real.sinc x ^ 4 = 2 * π / 3 := by
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp at h1
    linarith
  rw [← h2]
  apply integral_congr_ae
  filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0:ℝ)))] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

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

