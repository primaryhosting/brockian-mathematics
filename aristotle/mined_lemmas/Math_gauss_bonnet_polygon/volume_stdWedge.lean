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

theorem volume_stdWedge (θ : ℝ) (h0 : 0 < θ) (hpi : θ < π) :
    volume {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2}
      = ENNReal.ofReal (2 * (π - θ) / 3) := by
  have m1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have m2 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have m3 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (⇑MeasurableEquiv.finTwoArrow))
      volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  have hΦ : MeasurePreserving (fun x : E3 => (x 0, (x 1, x 2))) volume volume :=
    (m3.comp m2).comp m1
  have hTo : IsOpen {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
      0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} := by
    have hset : {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
        0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2}
        = ({q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1} ∩ {q : ℝ × (ℝ × ℝ) | 0 < q.2.1})
          ∩ {q : ℝ × (ℝ × ℝ) | 0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} := by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hpre : {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2}
      = (fun x : E3 => (x 0, (x 1, x 2))) ⁻¹'
        {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
          0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three,
      Real.norm_eq_abs, sq_abs, and_congr_left_iff]
    intro _
    simpa using Real.sqrt_lt' (x := y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) (y := 1) one_pos
  rw [hpre, hΦ.measure_preimage hTo.measurableSet.nullMeasurableSet, volume_wedge3 θ h0 hpi]

/-- The volume of the cone over a lune of angle `π - θ`, where `θ` is the angle between the
two normals. -/
