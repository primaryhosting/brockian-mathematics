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

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma lintegral_satoTateDensity_Icc {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ x in Set.Icc a b, ENNReal.ofReal (satoTateDensity x) =
      ENNReal.ofReal ((b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi) := by
  have hcont : Continuous satoTateDensity := by unfold satoTateDensity; fun_prop
  have hint : IntegrableOn satoTateDensity (Set.Icc a b) := hcont.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall satoTateDensity_nonneg)]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  unfold satoTateDensity
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The Sato–Tate mass of an interval is nonnegative. -/
