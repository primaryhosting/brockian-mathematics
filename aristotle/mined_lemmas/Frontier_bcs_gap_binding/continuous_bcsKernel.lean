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

set_option maxHeartbeats 1000000

namespace Frontier

/-- The BCS gap functional: the integral
`∫_0^ω dξ / √(ξ² + Δ²)` appearing in the (zero-temperature, constant density of states,
Debye-cutoff `ω`) BCS gap equation `1 = λ ∫_0^ω dξ / √(ξ² + Δ²)`. -/

theorem continuous_bcsKernel (Δ : ℝ) (hΔ : 0 < Δ) :
    Continuous fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) := by
  apply Continuous.div continuous_const
  · exact (Real.continuous_sqrt.comp (by continuity))
  · intro x
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))

/-- Closed form of the BCS gap integral: `∫_0^ω dξ / √(ξ² + Δ²) = arsinh (ω / Δ)`. -/
