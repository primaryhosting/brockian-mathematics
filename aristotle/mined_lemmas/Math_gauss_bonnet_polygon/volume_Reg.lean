import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem volume_Reg (u v w : E3) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ∀ r : ℝ, v ≠ r • u) (huw : ∀ r : ℝ, w ≠ r • u) (hvw : ∀ r : ℝ, w ≠ r • v) :
    3 * (volume (Reg u v w)).toReal
      = (π - angle v w) + (π - angle u w) + (π - angle u v) - π := by
  have hw : w ≠ 0 := by simpa using huw 0
  -- the three splittings
  have hA : Wdg u w ∩ Hs v = Reg u v w := by
    ext x; simp only [Reg, Wdg, mem_inter_iff]; tauto
  have hB : Wdg u w ∩ Hs (-v) = Reg u (-v) w := by
    ext x; simp only [Reg, Wdg, mem_inter_iff]; tauto
  have hC : Wdg v w ∩ Hs u = Reg u v w := by
    ext x; simp only [Reg, Wdg, mem_inter_iff]; tauto
  have hD : Wdg v w ∩ Hs (-u) = Reg (-u) v w := by
    ext x; simp only [Reg, Wdg, mem_inter_iff]; tauto
  have e2 : volume (Wdg u w) = volume (Reg u v w) + volume (Reg u (-v) w) := by
    rw [← hA, ← hB]; exact volume_split (measurableSet_Wdg u w) hv
  have e3 : volume (Wdg v w) = volume (Reg u v w) + volume (Reg (-u) v w) := by
    rw [← hC, ← hD]; exact volume_split (measurableSet_Wdg v w) hu
  have e4 : volume (Wdg u (-v)) = volume (Reg u (-v) w) + volume (Reg u (-v) (-w)) :=
    volume_split (measurableSet_Wdg u (-v)) hw
  have e6 : volume (Reg u (-v) (-w)) = volume (Reg (-u) v w) := by
    have := volume_Reg_neg (-u) v w
    simpa using this
  -- values of the wedges
  have w2 : volume (Wdg u w) = ENNReal.ofReal (2 / 3 * (π - angle u w)) := volume_Wdg u w hu huw
  have w3 : volume (Wdg v w) = ENNReal.ofReal (2 / 3 * (π - angle v w)) := volume_Wdg v w hv hvw
  have w4 : volume (Wdg u (-v)) = ENNReal.ofReal (2 / 3 * (angle u v)) := by
    rw [volume_Wdg u (-v) hu (fun r hr => huv (-r) (by rw [neg_smul, ← hr, neg_neg])),
      angle_neg_right]
    congr 1
    ring
  -- pass to real numbers
  have hpos2 : 0 ≤ 2 / 3 * (π - angle u w) := by
    have := angle_le_pi u w; linarith
  have hpos3 : 0 ≤ 2 / 3 * (π - angle v w) := by
    have := angle_le_pi v w; linarith
  have hpos4 : 0 ≤ 2 / 3 * (angle u v) := by
    have := angle_nonneg u v; linarith
  have t2 := congrArg ENNReal.toReal e2
  have t3 := congrArg ENNReal.toReal e3
  have t4 := congrArg ENNReal.toReal e4
  have t6 := congrArg ENNReal.toReal e6
  rw [w2, ENNReal.toReal_add (volume_Reg_ne_top _ _ _) (volume_Reg_ne_top _ _ _),
    ENNReal.toReal_ofReal hpos2] at t2
  rw [w3, ENNReal.toReal_add (volume_Reg_ne_top _ _ _) (volume_Reg_ne_top _ _ _),
    ENNReal.toReal_ofReal hpos3] at t3
  rw [w4, ENNReal.toReal_add (volume_Reg_ne_top _ _ _) (volume_Reg_ne_top _ _ _),
    ENNReal.toReal_ofReal hpos4] at t4
  linarith

end Math

import RequestProject.Sector

/-!
# Volume of a wedge in the unit ball of `ℝ³`

The intersection of the open unit ball of `ℝ³` with two half-spaces through the origin whose
boundary planes make a dihedral angle `π - θ` has volume `2/3 * (π - θ)`.
-/

open MeasureTheory Metric Set Real WithLp

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

