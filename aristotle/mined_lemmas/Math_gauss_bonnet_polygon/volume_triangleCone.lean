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

theorem volume_triangleCone {u v w : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : u ≠ v) (huv' : u ≠ -v) (hvw : v ≠ w) (hvw' : v ≠ -w) (huw : u ≠ w) (huw' : u ≠ -w) :
    (volume (hemiCone u ∩ hemiCone v ∩ hemiCone w)).toReal =
      (2 * π - InnerProductGeometry.angle u v - InnerProductGeometry.angle v w
        - InnerProductGeometry.angle w u) / 3 := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have msub : ∀ p q r : E3, hemiCone p ∩ hemiCone q ∩ hemiCone r ⊆ {x : E3 | ‖x‖ < 1} :=
    fun p q r _ hx => hx.1.1.1
  have msub2 : ∀ p q : E3, hemiCone p ∩ hemiCone q ⊆ {x : E3 | ‖x‖ < 1} := fun p q _ hx => hx.1.1
  have hmeas2 : ∀ p q : E3, MeasurableSet (hemiCone p ∩ hemiCone q) :=
    fun p q => (measurableSet_hemiCone p).inter (measurableSet_hemiCone q)
  have f : ∀ p q r : E3, volume (hemiCone p ∩ hemiCone q ∩ hemiCone r) ≠ ⊤ :=
    fun p q r => volume_ne_top_of_subset_ball (msub p q r)
  -- permutations of the three half-balls
  have p1 : hemiCone u ∩ hemiCone w ∩ hemiCone v = hemiCone u ∩ hemiCone v ∩ hemiCone w :=
    Set.inter_right_comm _ _ _
  have p3 : hemiCone u ∩ hemiCone w ∩ hemiCone (-v) = hemiCone u ∩ hemiCone (-v) ∩ hemiCone w :=
    Set.inter_right_comm _ _ _
  have p2 : hemiCone v ∩ hemiCone w ∩ hemiCone u = hemiCone u ∩ hemiCone v ∩ hemiCone w := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  have p4 : -(hemiCone v ∩ hemiCone w ∩ hemiCone (-u))
      = hemiCone u ∩ hemiCone (-v) ∩ hemiCone (-w) := by
    ext x
    simp only [Set.mem_neg, Set.mem_inter_iff, hemiCone, Set.mem_setOf_eq, inner_neg_left,
      norm_neg, inner_neg_right, neg_neg]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨-, h3⟩⟩, ⟨-, h4⟩⟩
      exact ⟨⟨⟨h1, by linarith⟩, h1, by linarith⟩, h1, by linarith⟩
    · rintro ⟨⟨⟨h1, h2⟩, ⟨-, h3⟩⟩, ⟨-, h4⟩⟩
      exact ⟨⟨⟨h1, by linarith⟩, h1, by linarith⟩, h1, by linarith⟩
  -- the lune volumes
  have hAuv := volume_lune hu hv huv huv'
  have hAuw := volume_lune hu hw huw huw'
  have hAvw := volume_lune hv hw hvw hvw'
  -- splittings
  have sA := volume_split_hemi (hemiCone u ∩ hemiCone v) (hmeas2 u v) (msub2 u v) hw0
  have sB := volume_split_hemi (hemiCone u ∩ hemiCone w) (hmeas2 u w) (msub2 u w) hv0
  have sC := volume_split_hemi (hemiCone v ∩ hemiCone w) (hmeas2 v w) (msub2 v w) hu0
  have sD := volume_split_hemi (hemiCone u) (measurableSet_hemiCone u) (hemiCone_subset_ball u) hv0
  have sF := volume_split_hemi (hemiCone u ∩ hemiCone (-v)) (hmeas2 u (-v)) (msub2 u (-v)) hw0
  rw [p1, p3] at sB
  have hanti : volume (hemiCone v ∩ hemiCone w ∩ hemiCone (-u))
      = volume (hemiCone u ∩ hemiCone (-v) ∩ hemiCone (-w)) := by
    rw [← p4, Measure.measure_neg]
  rw [p2, hanti] at sC
  rw [sA, sF] at sD
  -- pass to real numbers
  have hpi := Real.pi_pos
  have eA : (volume (hemiCone u ∩ hemiCone v ∩ hemiCone w)).toReal
      + (volume (hemiCone u ∩ hemiCone v ∩ hemiCone (-w))).toReal
      = 2 * (π - InnerProductGeometry.angle u v) / 3 := by
    rw [← ENNReal.toReal_add (f u v w) (f u v (-w)), ← sA, hAuv,
      ENNReal.toReal_ofReal (by linarith [InnerProductGeometry.angle_le_pi u v])]
  have eB : (volume (hemiCone u ∩ hemiCone v ∩ hemiCone w)).toReal
      + (volume (hemiCone u ∩ hemiCone (-v) ∩ hemiCone w)).toReal
      = 2 * (π - InnerProductGeometry.angle u w) / 3 := by
    rw [← ENNReal.toReal_add (f u v w) (f u (-v) w), ← sB, hAuw,
      ENNReal.toReal_ofReal (by linarith [InnerProductGeometry.angle_le_pi u w])]
  have eC : (volume (hemiCone u ∩ hemiCone v ∩ hemiCone w)).toReal
      + (volume (hemiCone u ∩ hemiCone (-v) ∩ hemiCone (-w))).toReal
      = 2 * (π - InnerProductGeometry.angle v w) / 3 := by
    rw [← ENNReal.toReal_add (f u v w) (f u (-v) (-w)), ← sC, hAvw,
      ENNReal.toReal_ofReal (by linarith [InnerProductGeometry.angle_le_pi v w])]
  have eD : ((volume (hemiCone u ∩ hemiCone v ∩ hemiCone w)).toReal
      + (volume (hemiCone u ∩ hemiCone v ∩ hemiCone (-w))).toReal)
      + ((volume (hemiCone u ∩ hemiCone (-v) ∩ hemiCone w)).toReal
      + (volume (hemiCone u ∩ hemiCone (-v) ∩ hemiCone (-w))).toReal) = 2 * π / 3 := by
    rw [← ENNReal.toReal_add (f u v w) (f u v (-w)),
      ← ENNReal.toReal_add (f u (-v) w) (f u (-v) (-w)),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f u v w, f u v (-w)⟩)
        (ENNReal.add_ne_top.mpr ⟨f u (-v) w, f u (-v) (-w)⟩),
      ← sD, volume_hemiCone hu0, ENNReal.toReal_ofReal (by positivity)]
  rw [InnerProductGeometry.angle_comm w u]; linarith

/-- The cone over the spherical triangle is, up to a null set, the intersection of the three
half-ball cones determined by the outer normals. -/
