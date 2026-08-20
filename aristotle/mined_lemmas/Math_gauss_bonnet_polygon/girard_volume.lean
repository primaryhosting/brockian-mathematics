import RequestProject.GaussBonnet.WedgeGeneral
import RequestProject.GaussBonnet.Angle
import RequestProject.GaussBonnet.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

**Girard's theorem** (the Gauss–Bonnet theorem for a geodesic triangle on the unit sphere):
the sum of the three interior angles of a spherical triangle exceeds `π` by its area.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The inward normal to the side `BC` of the spherical triangle `ABC`, normalised so that
`⟪A, nrm A B C⟫ = 1`. -/

theorem girard_volume (u v w : E3) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    volume (wedgeSet u v) + volume (wedgeSet v w) + volume (wedgeSet w u)
      + volume (wedgeSet (-u) (-v)) + volume (wedgeSet (-v) (-w)) + volume (wedgeSet (-w) (-u))
      = volume (closedBall (0 : E3) 1) + 4 * volume (octantSet u v w) := by
  -- half spaces are measurable
  have hHmeas : ∀ z : E3, MeasurableSet {x : E3 | 0 ≤ ⟪x, z⟫} := by
    intro z
    have h : Continuous fun x : E3 => ⟪x, z⟫ := by
      simpa [real_inner_comm] using (innerSL ℝ z).continuous
    exact (isClosed_le continuous_const h).measurableSet
  have hWmeas : ∀ a b : E3, MeasurableSet (wedgeSet a b) := by
    intro a b
    have h : wedgeSet a b
        = {x : E3 | ‖x‖ ≤ 1} ∩ ({x : E3 | 0 ≤ ⟪x, a⟫} ∩ {x : E3 | 0 ≤ ⟪x, b⟫}) := by
      ext x; simp [wedgeSet]
    rw [h]
    exact ((isClosed_le continuous_norm continuous_const).measurableSet).inter
      ((hHmeas a).inter (hHmeas b))
  -- hyperplanes are null
  have hnull : ∀ z : E3, z ≠ 0 → volume {x : E3 | ⟪x, z⟫ = 0} = 0 := by
    intro z hz
    have h : {x : E3 | ⟪x, z⟫ = 0}
        = (LinearMap.ker ((innerSL ℝ z).toLinearMap) : Submodule ℝ E3) := by
      ext x; simp [real_inner_comm]
    rw [h]
    apply Measure.addHaar_submodule
    intro htop
    have hz2 : z ∈ LinearMap.ker ((innerSL ℝ z).toLinearMap) := by rw [htop]; trivial
    simp at hz2
    exact hz hz2
  -- splitting a measurable set by a hyperplane through the origin
  have split : ∀ S : Set E3, MeasurableSet S → ∀ z : E3, z ≠ 0 →
      volume S = volume (S ∩ {x : E3 | 0 ≤ ⟪x, z⟫}) + volume (S ∩ {x : E3 | 0 ≤ ⟪x, -z⟫}) := by
    intro S hS z hz
    have hcover : S = (S ∩ {x : E3 | 0 ≤ ⟪x, z⟫}) ∪ (S ∩ {x : E3 | 0 ≤ ⟪x, -z⟫}) := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, inner_neg_right,
        Left.nonneg_neg_iff]
      constructor
      · intro hx
        rcases le_total 0 ⟪x, z⟫ with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    have hdisj : volume ((S ∩ {x : E3 | 0 ≤ ⟪x, z⟫}) ∩ (S ∩ {x : E3 | 0 ≤ ⟪x, -z⟫})) = 0 := by
      apply measure_mono_null _ (hnull z hz)
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, inner_neg_right, Left.nonneg_neg_iff] at hx
      exact le_antisymm hx.2.2 hx.1.2
    conv_lhs => rw [hcover]
    exact measure_union₀ (hS.inter (hHmeas (-z))).nullMeasurableSet hdisj
  -- the three levels of splitting
  have hsplitO : ∀ a b c : E3, c ≠ 0 →
      volume (wedgeSet a b) = volume (octantSet a b c) + volume (octantSet a b (-c)) := by
    intro a b c hc
    have h1 : wedgeSet a b ∩ {x : E3 | 0 ≤ ⟪x, c⟫} = octantSet a b c := by
      ext x; simp [wedgeSet, octantSet, and_assoc]
    have h2 : wedgeSet a b ∩ {x : E3 | 0 ≤ ⟪x, -c⟫} = octantSet a b (-c) := by
      ext x; simp [wedgeSet, octantSet, and_assoc]
    rw [split (wedgeSet a b) (hWmeas a b) c hc, h1, h2]
  have hsplitW : ∀ a b : E3, b ≠ 0 →
      volume (wedgeSet a a) = volume (wedgeSet a b) + volume (wedgeSet a (-b)) := by
    intro a b hb
    have h1 : wedgeSet a a ∩ {x : E3 | 0 ≤ ⟪x, b⟫} = wedgeSet a b := by
      ext x; simp [wedgeSet, and_assoc]
    have h2 : wedgeSet a a ∩ {x : E3 | 0 ≤ ⟪x, -b⟫} = wedgeSet a (-b) := by
      ext x; simp [wedgeSet, and_assoc]
    rw [split (wedgeSet a a) (hWmeas a a) b hb, h1, h2]
  have hsplitK : volume (closedBall (0 : E3) 1)
      = volume (wedgeSet u u) + volume (wedgeSet (-u) (-u)) := by
    have h1 : closedBall (0 : E3) 1 ∩ {x : E3 | 0 ≤ ⟪x, u⟫} = wedgeSet u u := by
      ext x; simp [wedgeSet, mem_closedBall, dist_zero_right]
    have h2 : closedBall (0 : E3) 1 ∩ {x : E3 | 0 ≤ ⟪x, -u⟫} = wedgeSet (-u) (-u) := by
      ext x; simp [wedgeSet, mem_closedBall, dist_zero_right]
    rw [split (closedBall (0 : E3) 1) measurableSet_closedBall u hu, h1, h2]
  have hperm : ∀ a b c : E3, octantSet a b c = octantSet c a b := by
    intro a b c; ext x; simp [octantSet]; tauto
  have hneg : volume (octantSet (-u) (-v) (-w)) = volume (octantSet u v w) := by
    have h : octantSet (-u) (-v) (-w) = -octantSet u v w := by
      ext x; simp [octantSet, inner_neg_right]
    rw [h, Measure.measure_neg]
  rw [hsplitK, hsplitW u v hv, hsplitW (-u) v hv,
    hsplitO u v w hw, hsplitO u (-v) w hw, hsplitO (-u) v w hw, hsplitO (-u) (-v) w hw,
    hsplitO v w u hu, hsplitO w u v hv, hsplitO (-v) (-w) u hu, hsplitO (-w) (-u) v hv,
    hperm v w u, hperm v w (-u), hperm w u v, hperm v w u, hperm w u (-v), hperm (-v) w u,
    hperm (-v) (-w) u, hperm (-v) (-w) (-u), hperm (-w) (-u) v, hperm v (-w) (-u),
    hperm (-w) (-u) (-v), hperm (-v) (-w) (-u), hneg]
  ring

end Math

import RequestProject.GaussBonnet.Defs

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file identifies the interior angle of a spherical triangle at a vertex with the
supplement of the angle between the normals of the two sides meeting at that vertex.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace

namespace Math

/-- The interior angle of the spherical triangle `A B C` at the vertex `C` is the supplement
of the angle between the normal vectors `B × C` and `C × A` of the two sides meeting at `C`. -/
