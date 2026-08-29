/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma satoTate_integral (f : ℝ → ℝ) :
    ∫ t, f t ∂satoTateMeasure = ∫ t in (0:ℝ)..Real.pi, satoTateDensity t * f t := by
  have hd : (fun θ => ENNReal.ofReal (satoTateDensity θ))
      = fun θ => ((Real.toNNReal (satoTateDensity θ) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [satoTateMeasure, hd,
    integral_withDensity_eq_integral_smul (by unfold satoTateDensity; fun_prop),
    intervalIntegral.integral_of_le Real.pi_nonneg, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  simp [NNReal.smul_def, Real.coe_toNNReal _ (satoTateDensity_nonneg x)]

/-- The first moment of the Sato–Tate distribution vanishes: `∫ 2cos θ dμ_ST = 0`. -/
