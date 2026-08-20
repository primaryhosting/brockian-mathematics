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

lemma sobolev_six_le (ψ : Space → ℂ) (h1 : ContDiff ℝ 1 ψ) (h2 : HasCompactSupport ψ) :
    (∫ x, ‖ψ x‖ ^ 6) ^ (1 / 6 : ℝ)
      ≤ sobolevConst * (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hmain := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℂ) (E := Space)
    (volume : Measure Space) h1 h2 (p := 2) (p' := 6) (by norm_num) (by simp) (by simp; norm_num)
  simp only [ENNReal.coe_ofNat] at hmain
  have hψ : MemLp ψ 6 (volume : Measure Space) := h1.continuous.memLp_of_hasCompactSupport h2
  have hcd : Continuous (fderiv ℝ ψ) := h1.continuous_fderiv (by norm_num)
  have hd : MemLp (fderiv ℝ ψ) 2 (volume : Measure Space) :=
    hcd.memLp_of_hasCompactSupport (h2.fderiv (𝕜 := ℝ))
  rw [hψ.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      hd.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hmain
  norm_num at hmain
  rw [show ((MeasureTheory.SNormLESNormFDerivOfEqConst ℂ (volume : Measure Space) 2 : NNReal)
        : ENNReal) = ENNReal.ofReal sobolevConst from ENNReal.ofReal_coe_nnreal.symm,
      ← ENNReal.ofReal_mul sobolevConst_nonneg] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg sobolevConst_nonneg
    (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _))).mp hmain

/-- Hölder interpolation of the `L^{10/3}` norm between `L²` and `L⁶`. -/
