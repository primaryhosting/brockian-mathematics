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

theorem energy_lower_bound_of_LT {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Kc b T V : ℝ} {ρ W : α → ℝ}
    (hKc : 0 < Kc) (hb : 0 ≤ b)
    (hρ : ∀ x, 0 ≤ ρ x) (hW : ∀ x, 0 ≤ W x)
    (hρint : Integrable (fun x => (ρ x) ^ (5 / 3 : ℝ)) μ)
    (hWρint : Integrable (fun x => W x * ρ x) μ)
    (hWint : Integrable (fun x => (W x) ^ (5 / 2 : ℝ)) μ)
    (hT : LTKineticBound μ Kc T ρ)
    (hV : AttractionBound μ b V W ρ) :
    -(ltConst Kc * b ^ (5 / 2 : ℝ) * ∫ x, (W x) ^ (5 / 2 : ℝ) ∂μ) ≤ T + V := by
  rw [LTKineticBound] at hT
  rw [AttractionBound] at hV
  have hpt : ∀ x, b * (W x * ρ x)
      ≤ Kc * (ρ x) ^ (5 / 3 : ℝ) + ltConst Kc * b ^ (5 / 2 : ℝ) * (W x) ^ (5 / 2 : ℝ) := by
    intro x
    have h := mul_le_rpow_five_thirds_add (Kc := Kc) (t := b * W x) (a := ρ x)
      hKc (mul_nonneg hb (hW x)) (hρ x)
    rw [Real.mul_rpow hb (hW x), ← mul_assoc] at h
    calc b * (W x * ρ x) = (b * W x) * ρ x := by ring
      _ ≤ _ := h
  have hint2 : Integrable (fun x => Kc * (ρ x) ^ (5 / 3 : ℝ)
      + ltConst Kc * b ^ (5 / 2 : ℝ) * (W x) ^ (5 / 2 : ℝ)) μ :=
    (hρint.const_mul Kc).add (hWint.const_mul _)
  have hmono := integral_mono (hWρint.const_mul b) hint2 hpt
  rw [integral_add (hρint.const_mul Kc) (hWint.const_mul _)] at hmono
  simp only [integral_const_mul] at hmono
  linarith

/-! ## The many-body setting in `ℝ³` -/

/-- Configuration space of one particle. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- The squared modulus of the gradient, `|∇ψ(x)|² = ∑ⱼ |∂ⱼψ(x)|²`. -/
