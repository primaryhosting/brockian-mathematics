/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

theorem lieb_thirring_stability
    {Kc b V : ℝ} {N : ℕ} {ψ : Fin N → Space → ℂ} {W : Space → ℝ}
    (hKc : 0 < Kc) (hb : 0 ≤ b)
    (hLT : LiebThirringKineticInequality Kc)
    (hadm : Admissible ψ)
    (hW : ∀ x, 0 ≤ W x)
    (hρint : Integrable (fun x => (density ψ x) ^ (5 / 3 : ℝ)))
    (hWρint : Integrable (fun x => W x * density ψ x))
    (hWint : Integrable (fun x => (W x) ^ (5 / 2 : ℝ)))
    (hV : -(b * ∫ x, W x * density ψ x) ≤ V) :
    -(ltConst Kc * b ^ (5 / 2 : ℝ) * ∫ x, (W x) ^ (5 / 2 : ℝ))
      ≤ (∑ i, kineticEnergy (ψ i)) + V :=
  energy_lower_bound_of_LT (μ := volume) hKc hb (density_nonneg ψ) hW hρint hWρint hWint
    (hLT N ψ hadm) hV

/-! ## The base case `N = 1` of the Lieb–Thirring kinetic inequality

For a single particle the Lieb–Thirring inequality reduces to the Sobolev inequality
`‖ψ‖_6 ≤ C ‖∇ψ‖_2` combined with the Hölder interpolation
`‖ψ‖_{10/3}^{10/3} ≤ ‖ψ‖_2^{4/3} ‖ψ‖_6^2`. We prove this base case unconditionally,
for `C¹` wave functions with compact support. -/

/-- The operator norm of the derivative is dominated by the Euclidean length of the
gradient. -/
