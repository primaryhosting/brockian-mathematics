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

theorem lieb_thirring_stability_linear
    {Kc b V A : ℝ} {K : ℕ} {N : ℕ} {ψ : Fin N → Space → ℂ} {W : Space → ℝ}
    (hKc : 0 < Kc) (hb : 0 ≤ b)
    (hLT : LiebThirringKineticInequality Kc)
    (hadm : Admissible ψ)
    (hW : ∀ x, 0 ≤ W x)
    (hρint : Integrable (fun x => (density ψ x) ^ (5 / 3 : ℝ)))
    (hWρint : Integrable (fun x => W x * density ψ x))
    (hWint : Integrable (fun x => (W x) ^ (5 / 2 : ℝ)))
    (hV : -(b * ∫ x, W x * density ψ x) ≤ V)
    (hA : (∫ x, (W x) ^ (5 / 2 : ℝ)) ≤ A * K) :
    -(ltConst Kc * b ^ (5 / 2 : ℝ) * A) * K ≤ (∑ i, kineticEnergy (ψ i)) + V := by
  have hC : 0 ≤ ltConst Kc * b ^ (5 / 2 : ℝ) :=
    mul_nonneg (ltConst_nonneg hKc) (Real.rpow_nonneg hb _)
  have h1 := lieb_thirring_stability hKc hb hLT hadm hW hρint hWρint hWint hV
  have h2 := mul_le_mul_of_nonneg_left hA hC
  linarith

end Frontier

