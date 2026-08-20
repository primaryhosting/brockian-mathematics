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

theorem lintegral_id_prod (r A B : ℝ) (hr : 0 < r) :
    ∫⁻ p in (Ioo (0:ℝ) r ×ˢ Ioo A B), ENNReal.ofReal p.1 = ENNReal.ofReal (r^2/2 * (B - A)) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    show (fun p : ℝ × ℝ => ENNReal.ofReal p.1) = (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * 1) by simp,
    MeasureTheory.lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal x) (g := fun _ : ℝ => 1)
      (by fun_prop) (by fun_prop)]
  simp [lintegral_id_Ioo r hr, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ r^2/2)]

/-- The area of the planar sector cut out by the two half-planes `{x > 0}` and
`{cos θ · x + sin θ · y > 0}` inside the disc of squared radius `R`. -/
