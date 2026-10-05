/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- For a `C¹` function with compact support on `ℝ`, the value at any point is bounded by the
total variation `∫ |f'|`. -/

lemma le_integral_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f)
    (x : ℝ) : f x ≤ ∫ t, |deriv f t| := by
  have hderiv_cont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hint : Integrable (deriv f) := hderiv_cont.integrable_of_hasCompactSupport h2f.deriv
  have hint' : Integrable (fun t => |deriv f t|) := hint.abs
  calc f x = ∫ t in Set.Iic x, deriv f t := (h2f.integral_Iic_deriv_eq hf x).symm
    _ ≤ ∫ t in Set.Iic x, |deriv f t| :=
        integral_mono hint.integrableOn hint'.integrableOn fun t => le_abs_self _
    _ ≤ ∫ t, |deriv f t| :=
        setIntegral_le_integral hint' (Filter.Eventually.of_forall fun t => abs_nonneg _)

/-- Cauchy–Schwarz inequality for integrals of continuous compactly supported functions on `ℝ`. -/
