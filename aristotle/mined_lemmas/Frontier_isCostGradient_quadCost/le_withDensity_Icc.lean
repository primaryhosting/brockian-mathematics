import Mathlib
/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem le_withDensity_Icc {g : ℝ → ℝ≥0∞} {lam : ℝ≥0} (hglb : ∀ x, (lam : ℝ≥0∞) ≤ g x)
    (a b : ℝ) :
    (lam : ℝ≥0∞) * ENNReal.ofReal (b - a) ≤ (volume.withDensity g) (Icc a b) := by
  rw [withDensity_apply _ measurableSet_Icc]
  calc (lam : ℝ≥0∞) * ENNReal.ofReal (b - a) = (lam : ℝ≥0∞) * volume (Icc a b) := by
        rw [Real.volume_Icc]
    _ = ∫⁻ _ in Icc a b, (lam : ℝ≥0∞) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in Icc a b, g t := lintegral_mono fun t => hglb t

/-- A measure with a density with respect to Lebesgue measure has no atoms. -/
