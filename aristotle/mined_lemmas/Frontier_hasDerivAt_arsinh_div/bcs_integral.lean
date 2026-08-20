import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
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


lemma bcs_integral (Δ ω : ℝ) (hΔ : 0 < Δ) :
    (∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) = Real.arsinh (ω / Δ) := by
  have hcont : ContinuousOn (fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) (Set.uIcc 0 ω) := by
    apply ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
    intro x _
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_arsinh_div Δ hΔ x)
      (hcont.intervalIntegrable)]
  simp

/-- **BCS gap equation has a nonzero solution for any attractive coupling.**
For coupling strength `g > 0` and Debye cutoff `ω > 0`, there is a strictly positive gap `Δ`
solving the (zero-temperature, constant density of states) BCS gap equation
`1 = g ∫₀^ω dξ / √(ξ² + Δ²)`; explicitly `Δ = ω / sinh (1/g)`. -/
