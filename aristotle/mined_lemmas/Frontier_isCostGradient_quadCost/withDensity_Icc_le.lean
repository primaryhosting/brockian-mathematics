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

theorem withDensity_Icc_le {f : ℝ → ℝ≥0∞} {Lam : ℝ≥0} (hfub : ∀ x, f x ≤ Lam) (a b : ℝ) :
    (volume.withDensity f) (Icc a b) ≤ (Lam : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  rw [withDensity_apply _ measurableSet_Icc]
  calc ∫⁻ t in Icc a b, f t ≤ ∫⁻ _ in Icc a b, (Lam : ℝ≥0∞) :=
        lintegral_mono fun t => hfub t
    _ = (Lam : ℝ≥0∞) * volume (Icc a b) := setLIntegral_const _ _
    _ = (Lam : ℝ≥0∞) * ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]

/-- A lower density bound gives a lower bound for the measure of an interval. -/
