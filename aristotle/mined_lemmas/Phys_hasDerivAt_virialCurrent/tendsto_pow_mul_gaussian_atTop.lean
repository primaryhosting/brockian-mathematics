import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

namespace Phys

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/

theorem tendsto_pow_mul_gaussian_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t ^ n * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  refine squeeze_zero' ?_ ?_ (h.comp hsq)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by nlinarith) n)
      (Real.exp_nonneg _)

/-- `x ^ n * exp (-x²) → 0` as `x → -∞`. -/
