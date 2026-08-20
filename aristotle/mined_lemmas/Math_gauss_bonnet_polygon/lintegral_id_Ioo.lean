/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem lintegral_id_Ioo (r : ℝ) (hr : 0 < r) :
    ∫⁻ x in Ioo (0:ℝ) r, ENNReal.ofReal x = ENNReal.ofReal (r^2/2) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    simp [integral_id]
  · exact (intervalIntegral.intervalIntegrable_id (μ := volume) (a := 0) (b := r)).1.mono_set
      Ioo_subset_Ioc_self
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx using hx.1.le

