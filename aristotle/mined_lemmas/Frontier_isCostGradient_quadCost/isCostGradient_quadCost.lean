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

theorem isCostGradient_quadCost :
    IsCostGradient (E := E) quadCost (fun x y => x - y) := by
  intro x y
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun x' : E => x' - y) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const y
  have h2 : HasFDerivAt (fun x' : E => ‖x' - y‖ ^ 2)
      (2 • ((innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E))) x := h1.norm_sq
  have h3 : HasFDerivAt (fun x' : E => ‖x' - y‖ ^ 2 / 2)
      ((2 : ℝ)⁻¹ • (2 • ((innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E)))) x := by
    simpa [div_eq_inv_mul] using h2.const_smul (2 : ℝ)⁻¹
  refine h3.congr_fderiv ?_
  ext z
  simp

/-- An affine function of `t` on `[0,1]` is bounded by the maximum of its endpoint values. -/
