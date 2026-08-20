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
noncomputable def nrm (A B C : E3) : E3 := (⟪A, cross B C⟫)⁻¹ • cross B C

/-- The area of the whole unit sphere is `4 * π`; this fixes the normalisation of `sphArea`. -/
theorem solid_sphere : solid (sphere (0 : E3) 1) = closedBall (0 : E3) 1 := by
  ext x
  simp only [solid, Set.mem_setOf_eq, mem_closedBall, dist_zero_right, mem_sphere_iff_norm,
    sub_zero, norm_smul, norm_inv, norm_norm]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (by field_simp [norm_ne_zero_iff.2 hx])

theorem sphArea_sphere : sphArea (sphere (0 : E3) 1) = 4 * π := by
  rw [sphArea, solid_sphere, volume_closedBall_E3, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The determinant `⟪A, B × C⟫` is invariant under cyclic permutations. -/
lemma det_cyclic (A B C : E3) : ⟪B, cross C A⟫ = ⟪A, cross B C⟫ := by
  simp only [inner_eq_three, cross_apply, crossProduct]
  simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

lemma det_ne_zero (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C]) :
    ⟪A, cross B C⟫ ≠ 0 := by
  intro h
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (![A, B, C] j).ofLp i with hM
  have hdet : M.det = ⟪A, cross B C⟫ := by
    rw [Matrix.det_fin_three]
    simp only [hM, Matrix.of_apply, inner_eq_three, cross_apply, crossProduct]
    simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := M)).2 (by rw [hdet, h])
  rw [Fintype.linearIndependent_iff] at hind
  have hsum : ∑ j, v j • (![A, B, C] j) = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct, hM, mul_comm] using congrFun hv i
  exact hv0 (funext fun i => hind v hsum i)

/-- The normal `nrm A B C` is orthogonal to `B` and `C` and normalised at `A`. -/
lemma inner_nrm (A B C : E3) (hd : ⟪A, cross B C⟫ ≠ 0) :
    ⟪A, nrm A B C⟫ = 1 ∧ ⟪B, nrm A B C⟫ = 0 ∧ ⟪C, nrm A B C⟫ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nrm, real_inner_smul_right, inv_mul_cancel₀ hd]
  · rw [nrm, real_inner_smul_right, real_inner_comm (cross B C) B, inner_cross_self_left, mul_zero]
  · rw [nrm, real_inner_smul_right, real_inner_comm (cross B C) C, inner_cross_self_right, mul_zero]

/-- The three normals form the basis dual to `A`, `B`, `C`. -/
lemma coords (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C]) (x : E3) :
    x = ⟪x, nrm A B C⟫ • A + ⟪x, nrm B C A⟫ • B + ⟪x, nrm C A B⟫ • C := by
  have hd := det_ne_zero A B C hind
  have hd2 : ⟪B, cross C A⟫ ≠ 0 := by rw [det_cyclic]; exact hd
  have hd3 : ⟪C, cross A B⟫ ≠ 0 := by rw [det_cyclic, det_cyclic]; exact hd
  set b := basisOfLinearIndependentOfCardEqFinrank hind (by simp) with hb
  have hbi : ⇑b = ![A, B, C] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hx : x = (b.repr x 0) • A + (b.repr x 1) • B + (b.repr x 2) • C := by
    have h := b.sum_repr x
    rw [Fin.sum_univ_three, hbi] at h
    simpa using h.symm
  obtain ⟨h1, h2, h3⟩ := inner_nrm A B C hd
  obtain ⟨k1, k2, k3⟩ := inner_nrm B C A hd2
  obtain ⟨l1, l2, l3⟩ := inner_nrm C A B hd3
  have e1 : ⟪x, nrm A B C⟫ = b.repr x 0 := by
    conv_lhs => rw [hx]
    simp only [inner_add_left, real_inner_smul_left, h1, h2, h3]
    ring
  have e2 : ⟪x, nrm B C A⟫ = b.repr x 1 := by
    conv_lhs => rw [hx]
    simp only [inner_add_left, real_inner_smul_left, k1, k2, k3]
    ring
  have e3 : ⟪x, nrm C A B⟫ = b.repr x 2 := by
    conv_lhs => rw [hx]
    simp only [inner_add_left, real_inner_smul_left, l1, l2, l3]
    ring
  rw [e1, e2, e3, ← hx]

/-- The solid cone over the spherical triangle is the intersection of the unit ball with the
three half spaces determined by the sides. -/
theorem solid_sphTriangle (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C]) :
    solid (sphTriangle A B C) = octantSet (nrm A B C) (nrm B C A) (nrm C A B) := by
  have hd := det_ne_zero A B C hind
  have hd2 : ⟪B, cross C A⟫ ≠ 0 := by rw [det_cyclic]; exact hd
  have hd3 : ⟪C, cross A B⟫ ≠ 0 := by rw [det_cyclic, det_cyclic]; exact hd
  obtain ⟨h1, h2, h3⟩ := inner_nrm A B C hd
  obtain ⟨k1, k2, k3⟩ := inner_nrm B C A hd2
  obtain ⟨l1, l2, l3⟩ := inner_nrm C A B hd3
  have key : ∀ x : E3, (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C) ↔
      (0 ≤ ⟪x, nrm A B C⟫ ∧ 0 ≤ ⟪x, nrm B C A⟫ ∧ 0 ≤ ⟪x, nrm C A B⟫) := by
    intro x
    constructor
    · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
      simp only [inner_add_left, real_inner_smul_left, h1, h2, h3, k1, k2, k3, l1, l2, l3]
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨p, q, r⟩
      exact ⟨_, _, _, p, q, r, coords A B C hind x⟩
  ext x
  simp only [solid, octantSet, sphTriangle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rcases h with rfl | h
    · simp
    · have hx : x ≠ 0 := by rintro rfl; simp at h
      have hpos : 0 < ‖x‖⁻¹ := by
        have : ‖x‖ > 0 := norm_pos_iff.2 hx
        positivity
      obtain ⟨-, hmem⟩ := h
      have hthis := (key _).1 hmem
      simp only [real_inner_smul_left] at hthis
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hthis.1, hthis.2.1, hthis.2.2]
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hpos : 0 < ‖x‖⁻¹ := by
        have : ‖x‖ > 0 := norm_pos_iff.2 hx
        positivity
      refine ⟨by simp [norm_smul]; field_simp, ?_⟩
      apply (key _).2
      simp only [real_inner_smul_left]
      exact ⟨mul_nonneg hpos.le hc.1, mul_nonneg hpos.le hc.2.1, mul_nonneg hpos.le hc.2.2⟩

/-- The analytic core of Girard's theorem, in terms of the three (nonzero) normal vectors. -/
lemma gauss_bonnet_aux (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C])
    (na nb nc : E3) (hna : na ≠ 0) (hnb : nb ≠ 0) (hnc : nc ≠ 0)
    (hnaa : na = nrm A B C) (hnbb : nb = nrm B C A) (hncc : nc = nrm C A B)
    (e1 : angle na nb = π - sphAngle C A B)
    (e2 : angle nb nc = π - sphAngle A B C)
    (e3 : angle nc na = π - sphAngle B C A) :
    sphAngle A B C + sphAngle B C A + sphAngle C A B = π + sphArea (sphTriangle A B C) := by
  set α := sphAngle A B C
  set β := sphAngle B C A
  set γ := sphAngle C A B
  obtain ⟨hα0, hαp⟩ : 0 ≤ α ∧ α ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  obtain ⟨hβ0, hβp⟩ : 0 ≤ β ∧ β ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  obtain ⟨hγ0, hγp⟩ : 0 ≤ γ ∧ γ ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  have hoct : octantSet na nb nc = solid (sphTriangle A B C) := by
    rw [hnaa, hnbb, hncc, solid_sphTriangle A B C hind]
  have g := girard_volume na nb nc hna hnb hnc
  rw [hoct] at g
  simp only [wedgeSet] at g
  rw [volume_wedge na nb hna hnb, volume_wedge nb nc hnb hnc, volume_wedge nc na hnc hna,
    volume_wedge (-na) (-nb) (neg_ne_zero.2 hna) (neg_ne_zero.2 hnb),
    volume_wedge (-nb) (-nc) (neg_ne_zero.2 hnb) (neg_ne_zero.2 hnc),
    volume_wedge (-nc) (-na) (neg_ne_zero.2 hnc) (neg_ne_zero.2 hna),
    angle_neg_neg, angle_neg_neg, angle_neg_neg, e1, e2, e3, volume_closedBall_E3] at g
  simp only [sub_sub_cancel] at g
  have hfin : volume (solid (sphTriangle A B C)) ≠ ⊤ := by
    have hsub : solid (sphTriangle A B C) ⊆ closedBall (0 : E3) 1 := by
      intro x hx
      simpa [mem_closedBall, dist_zero_right] using hx.1
    exact ne_top_of_le_ne_top (by rw [volume_closedBall_E3]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono hsub)
  set V := (volume (solid (sphTriangle A B C))).toReal with hV
  have hVe : volume (solid (sphTriangle A B C)) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hfin]
  rw [hVe] at g
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  have hpi := Real.pi_pos
  rw [← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)] at g
  rw [show (4 : ENNReal) = ENNReal.ofReal 4 by simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)] at g
  rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) (by positivity)] at g
  rw [sphArea, ← hV]
  linarith

/-- **Gauss–Bonnet / Girard's theorem for a spherical triangle.**
The sum of the interior angles of a geodesic triangle on the unit sphere exceeds `π`
by the area of the triangle. -/
theorem gauss_bonnet_polygon (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hind : LinearIndependent ℝ ![A, B, C]) :
    sphAngle A B C + sphAngle B C A + sphAngle C A B = π + sphArea (sphTriangle A B C) := by
  have hd := det_ne_zero A B C hind
  have hd2 : ⟪B, cross C A⟫ ≠ 0 := by rw [det_cyclic]; exact hd
  have hd3 : ⟪C, cross A B⟫ ≠ 0 := by rw [det_cyclic, det_cyclic]; exact hd
  have hnbeq : nrm B C A = (⟪A, cross B C⟫)⁻¹ • cross C A := by rw [nrm, det_cyclic]
  have hnceq : nrm C A B = (⟪A, cross B C⟫)⁻¹ • cross A B := by rw [nrm, det_cyclic, det_cyclic]
  have hnonzero : ∀ X Y Z : E3, ⟪X, cross Y Z⟫ ≠ 0 → nrm X Y Z ≠ 0 := by
    intro X Y Z h hz
    have h1 := (inner_nrm X Y Z h).1
    rw [hz, inner_zero_right] at h1
    exact zero_ne_one h1
  have e1 : angle (nrm A B C) (nrm B C A) = π - sphAngle C A B := by
    rw [nrm, hnbeq, angle_smul_smul (inv_ne_zero hd), angle_cross_cross A B C hA hB hC]
  have e2 : angle (nrm B C A) (nrm C A B) = π - sphAngle A B C := by
    rw [hnbeq, hnceq, angle_smul_smul (inv_ne_zero hd), angle_cross_cross B C A hB hC hA]
  have e3 : angle (nrm C A B) (nrm A B C) = π - sphAngle B C A := by
    rw [hnceq, nrm, angle_smul_smul (inv_ne_zero hd), angle_cross_cross C A B hC hA hB]
  exact gauss_bonnet_aux A B C hind _ _ _ (hnonzero A B C hd) (hnonzero B C A hd2)
    (hnonzero C A B hd3) rfl rfl rfl e1 e2 e3

end Math

import Mathlib

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

import RequestProject.GaussBonnet.Defs

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Girard's combinatorial decomposition of the ball into six solid lunes.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The solid wedge cut out of the unit ball by the half spaces `0 ≤ ⟪x, u⟫`, `0 ≤ ⟪x, v⟫`. -/
def wedgeSet (u v : E3) : Set E3 := {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫}

/-- The solid cone cut out of the unit ball by three half spaces through the origin. -/
def octantSet (u v w : E3) : Set E3 :=
  {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫ ∧ 0 ≤ ⟪x, w⟫}

/-- **Girard's decomposition.**  The six solid lunes determined by three planes through the
origin cover the ball once, except for the two opposite solid triangles, which are covered
three times. -/
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
theorem angle_cross_cross (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) :
    angle (cross B C) (cross C A) = π - sphAngle C A B := by
  have hAC : ⟪A, C⟫ = ⟪C, A⟫ := real_inner_comm C A
  have hBC : ⟪B, C⟫ = ⟪C, B⟫ := real_inner_comm C B
  have hBA : ⟪B, A⟫ = ⟪A, B⟫ := real_inner_comm A B
  have hn1 : ‖cross B C‖ = √(1 - ⟪C, B⟫ ^ 2) := by
    have h : ‖cross B C‖ ^ 2 = 1 - ⟪C, B⟫ ^ 2 := by rw [norm_cross_sq, hB, hC, hBC]; ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hn2 : ‖cross C A‖ = √(1 - ⟪C, A⟫ ^ 2) := by
    have h : ‖cross C A‖ ^ 2 = 1 - ⟪C, A⟫ ^ 2 := by rw [norm_cross_sq, hC, hA]; ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hi : ⟪cross B C, cross C A⟫ = ⟪C, B⟫ * ⟪C, A⟫ - ⟪A, B⟫ := by
    rw [inner_cross_cross, real_inner_self_eq_norm_sq, hC, hBC, hBA]; ring
  have ha : ‖A - ⟪C, A⟫ • C‖ = √(1 - ⟪C, A⟫ ^ 2) := by
    have h : ‖A - ⟪C, A⟫ • C‖ ^ 2 = 1 - ⟪C, A⟫ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hA, hC, hAC]
      simp
      ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hb : ‖B - ⟪C, B⟫ • C‖ = √(1 - ⟪C, B⟫ ^ 2) := by
    have h : ‖B - ⟪C, B⟫ • C‖ ^ 2 = 1 - ⟪C, B⟫ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hB, hC, hBC]
      simp
      ring
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hab : ⟪A - ⟪C, A⟫ • C, B - ⟪C, B⟫ • C⟫ = ⟪A, B⟫ - ⟪C, A⟫ * ⟪C, B⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hC, hAC]
    ring
  show Real.arccos _ = π - Real.arccos _
  rw [hi, hn1, hn2, hab, ha, hb, ← Real.arccos_neg]
  congr 1
  rw [mul_comm (√(1 - ⟪C, B⟫ ^ 2)), ← neg_div]
  ring_nf

end Math

import RequestProject.GaussBonnet.Defs

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file computes the volume of a solid wedge (the intersection of the unit ball of `E3`
with two half spaces through the origin).
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric Pointwise

namespace Math

/-- The volume of the unit ball of `E3`. -/
lemma volume_closedBall_E3 : volume (closedBall (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin]
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = 3 / 2 + 1 by norm_num]
  rw [Real.Gamma_add_one (by norm_num), show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h : Real.sqrt π ^ 3 = π * Real.sqrt π := by rw [pow_succ, sq_sqrt Real.pi_nonneg]
  have hs : Real.sqrt π > 0 := Real.sqrt_pos.2 Real.pi_pos
  rw [h]
  field_simp
  ring

/-- The area of a circular sector of the unit disc, cut out by the two half planes
`0 ≤ x` and `0 ≤ x cos f + y sin f`. -/
lemma volume_sector (f : ℝ) (hf0 : 0 ≤ f) (hfpi : f ≤ π) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
      = ENNReal.ofReal ((π - f) / 2) := by
  rcases eq_or_lt_of_le hfpi with rfl | hfpi
  · -- degenerate case: the sector is a segment, of measure zero
    have hsub : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ cos π * p.1 + sin π * p.2}
        ⊆ ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      rintro ⟨x, y⟩ ⟨-, h2, h3⟩
      simp only [Real.cos_pi, Real.sin_pi] at h3
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      simp at h2 h3 ⊢
      linarith
    have h0 : volume (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
      simp
    rw [measure_mono_null hsub h0]
    simp
  set S := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2} with hS
  set A : Set (ℝ × ℝ) := Set.Ioc (0:ℝ) 1 ×ˢ Set.Icc (f - π/2) (π/2) with hA
  have htrig : ∀ θ ∈ Set.Ioo (-π) π, (0 ≤ cos θ ∧ 0 ≤ cos f * cos θ + sin f * sin θ) ↔
      (f - π/2 ≤ θ ∧ θ ≤ π/2) := by
    intro θ hθ
    have hcs : cos f * cos θ + sin f * sin θ = cos (θ - f) := by rw [Real.cos_sub]; ring
    rw [hcs]
    constructor
    · rintro ⟨h1, h2⟩
      have hθu : θ ≤ π/2 := by
        by_contra h
        push_neg at h
        have := Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [hθ.2, Real.pi_pos])
        linarith
      refine ⟨?_, hθu⟩
      by_contra h
      push_neg at h
      have hθl : -(π/2) ≤ θ := by
        by_contra h'
        push_neg at h'
        have : cos (-θ) < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hθ.1])
        rw [Real.cos_neg] at this; linarith
      have : cos (-(θ - f)) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
      rw [Real.cos_neg] at this; linarith
    · rintro ⟨h1, h2⟩
      exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩,
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩
  have hSmeas : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {p : ℝ × ℝ | (0:ℝ) ≤ p.1} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h3 : MeasurableSet {p : ℝ × ℝ | (0:ℝ) ≤ cos f * p.1 + sin f * p.2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact (h1.inter (h2.inter h3))
  have hAmeas : MeasurableSet A := measurableSet_Ioc.prod measurableSet_Icc
  have hAsub : A ⊆ polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioc] at hr
    simp only [Set.mem_Icc] at hθ
    exact ⟨hr.1, Set.mem_Ioo.2 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (S.indicator (1 : ℝ × ℝ → ENNReal)) (polarCoord.symm p)
        = A.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hrpos : 0 < r := hr
    have hsymm : polarCoord.symm (r, θ) = (r * cos θ, r * sin θ) := rfl
    have hsq : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hmem : polarCoord.symm (r, θ) ∈ S ↔ (r, θ) ∈ A := by
      rw [hsymm, hS, hA]
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [hsq] at h1
        have hr1 : r ≤ 1 := by nlinarith
        exact ⟨⟨hrpos, hr1⟩, (htrig θ hθ).1 ⟨by nlinarith, by nlinarith⟩⟩
      · rintro ⟨⟨-, hr1⟩, hθ2⟩
        obtain ⟨c1, c2⟩ := (htrig θ hθ).2 hθ2
        exact ⟨by rw [hsq]; nlinarith, by nlinarith, by nlinarith⟩
    by_cases h : (r, θ) ∈ A
    · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem h]
      simp
    · rw [Set.indicator_of_notMem (fun hc => h (hmem.1 hc)), Set.indicator_of_notMem h]
      simp
  have hone : ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal x = ENNReal.ofReal (1/2) := by
    have h := ofReal_integral_eq_lintegral_ofReal
        ((by fun_prop : Continuous fun x : ℝ => x).integrableOn_Ioc
          (a := (0:ℝ)) (b := 1) (μ := volume))
        ((ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0:ℝ)) (b := 1))).mono
          (fun x hx => le_of_lt hx.1))
    rw [← h]
    congr 1
    rw [← intervalIntegral.integral_of_le (by norm_num)]
    simp
  calc volume S
      = ∫⁻ p, (S.indicator (1 : ℝ × ℝ → ENNReal)) p := (lintegral_indicator_one hSmeas).symm
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • (S.indicator (1 : ℝ × ℝ → ENNReal)) (polarCoord.symm p) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in polarCoord.target, A.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p :=
        setLIntegral_congr_fun polarCoord.open_target.measurableSet key
    _ = ∫⁻ p in A, ENNReal.ofReal p.1 := by
        rw [setLIntegral_indicator hAmeas, Set.inter_eq_left.2 hAsub]
    _ = ENNReal.ofReal ((π - f)/2) := by
        rw [hA, MeasureTheory.Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod _ (by fun_prop)]
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        rw [lintegral_mul_const _ (by fun_prop), hone, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- The area of the circular sector of the disc of radius `√R`, cut out by the two half
planes `0 ≤ x` and `0 ≤ x cos f + y sin f`. -/
lemma volume_sector_scaled (f R : ℝ) (hf0 : 0 ≤ f) (hfpi : f ≤ π) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
      = ENNReal.ofReal (R * ((π - f) / 2)) := by
  rcases le_or_gt R 0 with hR | hR
  · have hsub : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
        ⊆ ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      rintro ⟨x, y⟩ ⟨h1, -, -⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      simp only at h1 ⊢
      nlinarith [sq_nonneg x, sq_nonneg y]
    have h0 : volume (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]; simp
    rw [measure_mono_null hsub h0, eq_comm, ENNReal.ofReal_eq_zero]
    nlinarith
  · set s := Real.sqrt R with hsdef
    have hs : 0 < s := Real.sqrt_pos.2 hR
    have hs2 : s ^ 2 = R := Real.sq_sqrt hR.le
    have hset : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
        = s • {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_smul_set]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨(s⁻¹ * p.1, s⁻¹ * p.2), ⟨?_, ?_, ?_⟩, ?_⟩
        · have h : (s⁻¹ * p.1) ^ 2 + (s⁻¹ * p.2) ^ 2 = (p.1 ^ 2 + p.2 ^ 2) / s ^ 2 := by field_simp
          rw [h, hs2, div_le_one hR]
          exact h1
        · positivity
        · have h : cos f * (s⁻¹ * p.1) + sin f * (s⁻¹ * p.2)
              = s⁻¹ * (cos f * p.1 + sin f * p.2) := by ring
          rw [h]; positivity
        · refine Prod.ext ?_ ?_ <;> simp [Prod.smul_mk] <;> field_simp
      · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · show (s * q.1) ^ 2 + (s * q.2) ^ 2 ≤ R
          nlinarith [sq_nonneg s]
        · show 0 ≤ s * q.1
          positivity
        · show 0 ≤ cos f * (s * q.1) + sin f * (s * q.2)
          have h : cos f * (s * q.1) + sin f * (s * q.2) = s * (cos f * q.1 + sin f * q.2) := by
            ring
          rw [h]; positivity
    rw [hset, Measure.addHaar_smul, volume_sector f hf0 hfpi]
    rw [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2), hs2, ← ENNReal.ofReal_mul hR.le]

/-- The integral of the cross sectional area factor `1 - t ^ 2` over the real line. -/
lemma lintegral_one_sub_sq : ∫⁻ (t : ℝ), ENNReal.ofReal (1 - t ^ 2) = ENNReal.ofReal (4 / 3) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (1 - t ^ 2) :=
    (measurable_const.sub (measurable_id.pow_const 2)).ennreal_ofReal
  rw [← lintegral_add_compl _ (measurableSet_Icc (a := (-1:ℝ)) (b := 1))]
  have h2 : ∫⁻ t in (Set.Icc (-1:ℝ) 1)ᶜ, ENNReal.ofReal (1 - t ^ 2) = 0 := by
    rw [setLIntegral_eq_zero_iff measurableSet_Icc.compl hmeas]
    filter_upwards with t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    show ENNReal.ofReal (1 - t ^ 2) = 0
    rw [ENNReal.ofReal_eq_zero]
    rcases ht with h | h <;> nlinarith
  rw [h2, add_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2).integrableOn_Icc
        (a := (-1:ℝ)) (b := 1) (μ := volume))
      ((ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (-1:ℝ)) (b := 1))).mono
        (fun t ht => by
          simp only [Set.mem_Icc] at ht
          show (0:ℝ) ≤ 1 - t ^ 2
          nlinarith [ht.1, ht.2]))]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  simp
  norm_num

/-- The volume of the standard wedge of dihedral angle `π - f` in the unit ball. -/
lemma volume_wedge_std (f : ℝ) (hf0 : 0 ≤ f) (hfpi : f ≤ π) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ x.ofLp 0 ∧ 0 ≤ cos f * x.ofLp 0 + sin f * x.ofLp 1}
      = ENNReal.ofReal (2 / 3 * (π - f)) := by
  set W' : Set (ℝ × (ℝ × ℝ)) :=
    {q | q.2.1 ^ 2 + q.2.2 ^ 2 + q.1 ^ 2 ≤ 1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ cos f * q.2.1 + sin f * q.2.2}
    with hW'
  have hcomp : ((Prod.map id ⇑(MeasurableEquiv.finTwoArrow (α := ℝ))) ∘
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)) ∘ (WithLp.ofLp))
      = (fun x : E3 => (x.ofLp 2, (x.ofLp 0, x.ofLp 1))) := by
    funext x; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> rfl
  have hPhi : MeasurePreserving
      (fun x : E3 => (x.ofLp 2, (x.ofLp 0, x.ofLp 1)) : E3 → ℝ × (ℝ × ℝ)) volume volume := by
    rw [← hcomp]
    apply MeasurePreserving.comp
    · exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
    · exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
        (PiLp.volume_preserving_ofLp (Fin 3))
  have hnorm : ∀ x : E3, ‖x‖ ^ 2 = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply (𝕜 := ℝ), Fin.sum_univ_three]
    simp [sq]
  have hW'meas : MeasurableSet W' := by
    have h1 : MeasurableSet {q : ℝ × (ℝ × ℝ) | q.2.1 ^ 2 + q.2.2 ^ 2 + q.1 ^ 2 ≤ 1} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {q : ℝ × (ℝ × ℝ) | (0:ℝ) ≤ q.2.1} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h3 : MeasurableSet {q : ℝ × (ℝ × ℝ) | (0:ℝ) ≤ cos f * q.2.1 + sin f * q.2.2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  have hpre : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ x.ofLp 0 ∧ 0 ≤ cos f * x.ofLp 0 + sin f * x.ofLp 1}
      = (fun x : E3 => (x.ofLp 2, (x.ofLp 0, x.ofLp 1)) : E3 → ℝ × (ℝ × ℝ)) ⁻¹' W' := by
    ext x
    simp only [hW', Set.mem_setOf_eq, Set.mem_preimage]
    have hx := hnorm x
    have hnn := norm_nonneg x
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by nlinarith, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by nlinarith, h2, h3⟩
  rw [hpre, hPhi.measure_preimage hW'meas.nullMeasurableSet,
    MeasureTheory.Measure.volume_eq_prod, Measure.prod_apply hW'meas]
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' W')
      = ENNReal.ofReal (1 - t ^ 2) * ENNReal.ofReal ((π - f) / 2) := by
    intro t
    have hs : Prod.mk t ⁻¹' W'
        = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 - t ^ 2 ∧ 0 ≤ p.1 ∧
            0 ≤ cos f * p.1 + sin f * p.2} := by
      ext p
      simp only [hW', Set.mem_preimage, Set.mem_setOf_eq]
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, h2, h3⟩
    rw [hs, volume_sector_scaled f _ hf0 hfpi, ENNReal.ofReal_mul' (by linarith)]
  simp only [hslice]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_one_sub_sq,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end Math

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace

namespace Math

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The cross product on `E3`. -/
noncomputable def cross (x y : E3) : E3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp x) (WithLp.ofLp y))

@[simp] lemma cross_apply (x y : E3) (i : Fin 3) :
    (cross x y).ofLp i = (crossProduct (WithLp.ofLp x) (WithLp.ofLp y)) i := rfl

lemma inner_eq_sum (x y : E3) : ⟪x, y⟫ = ∑ i, x.ofLp i * y.ofLp i := by
  simp [PiLp.inner_apply (𝕜 := ℝ), mul_comm]

lemma inner_eq_three (x y : E3) :
    ⟪x, y⟫ = x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1 + x.ofLp 2 * y.ofLp 2 := by
  rw [inner_eq_sum, Fin.sum_univ_three]

/-- Binet–Cauchy identity for the cross product. -/
lemma inner_cross_cross (x y z w : E3) :
    ⟪cross x y, cross z w⟫ = ⟪x, z⟫ * ⟪y, w⟫ - ⟪x, w⟫ * ⟪y, z⟫ := by
  simp only [inner_eq_three, cross_apply, crossProduct]
  simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

lemma inner_cross_self_left (x y : E3) : ⟪cross x y, x⟫ = 0 := by
  simp only [inner_eq_three, cross_apply, crossProduct]
  simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

lemma inner_cross_self_right (x y : E3) : ⟪cross x y, y⟫ = 0 := by
  simp only [inner_eq_three, cross_apply, crossProduct]
  simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

lemma norm_cross_sq (x y : E3) : ‖cross x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_cross_cross, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  ring_nf
  rw [real_inner_comm y x]
  ring

/-- The solid cone over a subset of the unit sphere. -/
def solid (S : Set E3) : Set E3 := {x | ‖x‖ ≤ 1 ∧ (x = 0 ∨ ‖x‖⁻¹ • x ∈ S)}

/-- The area of a subset of the unit sphere, defined as three times the volume of the
solid cone over it.  (For the whole sphere this gives `4 * π`, see `sphArea_sphere`.) -/
noncomputable def sphArea (S : Set E3) : ℝ := 3 * (volume (solid S)).toReal

/-- The (closed) spherical triangle with vertices `A`, `B`, `C`: the set of unit vectors
lying in the cone positively spanned by `A`, `B`, `C`. -/
def sphTriangle (A B C : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C}

/-- The interior angle at the vertex `A` of the spherical triangle `A B C`: the Euclidean
angle between the tangent vectors at `A` of the geodesics `A → B` and `A → C`, i.e. between
the projections of `B` and `C` to the plane orthogonal to `A`. -/
noncomputable def sphAngle (A B C : E3) : ℝ :=
  InnerProductGeometry.angle (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)

end Math

import RequestProject.GaussBonnet.Wedge

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Volume of a general solid wedge, obtained from the standard one by an isometry.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- Any unit vector `v` can be written as `cos f • u + sin f • w` for a unit vector `w`
orthogonal to the unit vector `u`, where `f` is the angle between `u` and `v`. -/
lemma exists_orthogonal_decomp (u v : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ w : E3, ‖w‖ = 1 ∧ ⟪u, w⟫ = 0 ∧ v = cos (angle u v) • u + sin (angle u v) • w := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have hex : ∃ w : E3, ‖w‖ = 1 ∧ ⟪u, w⟫ = 0 := by
    haveI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    have hf : Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E3) = 2 :=
      Submodule.finrank_orthogonal_span_singleton hu0
    have hne : ((ℝ ∙ u)ᗮ : Submodule ℝ E3) ≠ ⊥ := by
      intro h; rw [h] at hf; simp at hf
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hip : ⟪u, p⟫ = 0 := by
      rw [Submodule.mem_orthogonal] at hp
      exact hp u (Submodule.mem_span_singleton_self u)
    exact ⟨‖p‖⁻¹ • p, by rw [norm_smul]; simp [norm_ne_zero_iff.2 hp0],
      by rw [real_inner_smul_right, hip, mul_zero]⟩
  set f := angle u v with hf
  have hcos : cos f = ⟪u, v⟫ := by rw [hf, cos_angle, hu, hv]; ring
  have hf0 : 0 ≤ f := angle_nonneg u v
  have hfpi : f ≤ π := angle_le_pi u v
  have hsin : sin f = ‖v - ⟪u, v⟫ • u‖ := by
    have h1 : ‖v - ⟪u, v⟫ • u‖ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, hv, real_inner_comm u v]
      simp
      ring
    rw [Real.sin_eq_sqrt_one_sub_cos_sq hf0 hfpi, hcos, ← h1, Real.sqrt_sq (norm_nonneg _)]
  by_cases hz : sin f = 0
  · obtain ⟨w, hw1, hw2⟩ := hex
    refine ⟨w, hw1, hw2, ?_⟩
    rw [hz, zero_smul, add_zero, hcos]
    have h3 : ‖v - ⟪u, v⟫ • u‖ = 0 := by rw [← hsin, hz]
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  · refine ⟨(sin f)⁻¹ • (v - ⟪u, v⟫ • u), ?_, ?_, ?_⟩
    · rw [norm_smul, ← hsin]
      simp [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hf0 hfpi), hz]
    · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu]
      simp
    · rw [smul_smul, mul_inv_cancel₀ hz, one_smul, hcos]
      module

/-- The standard wedge is measurable. -/
lemma measurableSet_std (f : ℝ) : MeasurableSet
    {y : E3 | ‖y‖ ≤ 1 ∧ 0 ≤ y.ofLp 0 ∧ 0 ≤ cos f * y.ofLp 0 + sin f * y.ofLp 1} := by
  have c0 : Continuous fun y : E3 => y.ofLp 0 := by fun_prop
  have h : {y : E3 | ‖y‖ ≤ 1 ∧ 0 ≤ y.ofLp 0 ∧ 0 ≤ cos f * y.ofLp 0 + sin f * y.ofLp 1}
      = {y : E3 | ‖y‖ ≤ 1} ∩ ({y : E3 | 0 ≤ y.ofLp 0} ∩
        {y : E3 | 0 ≤ cos f * y.ofLp 0 + sin f * y.ofLp 1}) := by
    ext y; simp
  rw [h]
  exact ((isClosed_le continuous_norm continuous_const).measurableSet).inter
    (((isClosed_le continuous_const c0).measurableSet).inter
      ((isClosed_le continuous_const (by fun_prop)).measurableSet))

/-- The volume of a solid wedge, for unit vectors. -/
lemma volume_wedge_unit (u v : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫}
      = ENNReal.ofReal (2 / 3 * (π - angle u v)) := by
  obtain ⟨w, hw1, huw, hvdecomp⟩ := exists_orthogonal_decomp u v hu hv
  have hwu : ⟪w, u⟫ = 0 := by rw [real_inner_comm u w, huw]
  have hcu : ⟪u, cross u w⟫ = 0 := by rw [real_inner_comm (cross u w) u, inner_cross_self_left]
  have hcw : ⟪w, cross u w⟫ = 0 := by rw [real_inner_comm (cross u w) w, inner_cross_self_right]
  have h1 : ‖cross u w‖ = 1 := by
    have h : ‖cross u w‖ ^ 2 = 1 := by rw [norm_cross_sq, hu, hw1, huw]; ring
    nlinarith [norm_nonneg (cross u w)]
  have hon : Orthonormal ℝ ![u, w, cross u w] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, hw1, huw, h1, hcu, hcw, hwu, inner_cross_self_left, inner_cross_self_right]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![u, w, cross u w]) := by
    have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
    have hcoe := coe_basisOfLinearIndependentOfCardEqFinrank hon.linearIndependent hcard
    have hs := (basisOfLinearIndependentOfCardEqFinrank hon.linearIndependent hcard).span_eq
    rw [hcoe] at hs
    exact le_of_eq hs.symm
  set b := OrthonormalBasis.mk hon hsp with hbdef
  have hb0 : b 0 = u := by rw [hbdef, OrthonormalBasis.coe_mk]; rfl
  have hb1 : b 1 = w := by rw [hbdef, OrthonormalBasis.coe_mk]; rfl
  have hpre : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫}
      = b.repr ⁻¹' {y : E3 | ‖y‖ ≤ 1 ∧ 0 ≤ y.ofLp 0 ∧
          0 ≤ cos (angle u v) * y.ofLp 0 + sin (angle u v) * y.ofLp 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, LinearIsometryEquiv.norm_map,
      OrthonormalBasis.repr_apply_apply, hb0, hb1]
    constructor
    · rintro ⟨hn, ha, hbb⟩
      rw [hvdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right] at hbb
      refine ⟨hn, ?_, ?_⟩
      · rw [real_inner_comm x u]; exact ha
      · rw [real_inner_comm x u, real_inner_comm x w]; exact hbb
    · rintro ⟨hn, ha, hbb⟩
      rw [real_inner_comm x u] at ha
      rw [real_inner_comm x u, real_inner_comm x w] at hbb
      refine ⟨hn, ha, ?_⟩
      rw [hvdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact hbb
  rw [hpre, (b.repr.measurePreserving).measure_preimage (measurableSet_std _).nullMeasurableSet,
    volume_wedge_std _ (angle_nonneg u v) (angle_le_pi u v)]

/-- **Volume of a solid wedge.**  If `u` and `v` are nonzero vectors, the intersection of the
unit ball with the two half spaces `0 ≤ ⟪x, u⟫` and `0 ≤ ⟪x, v⟫` has volume
`2/3 * (π - angle u v)`. -/
theorem volume_wedge (u v : E3) (hu : u ≠ 0) (hv : v ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫}
      = ENNReal.ofReal (2 / 3 * (π - angle u v)) := by
  have hun : (0 : ℝ) < ‖u‖⁻¹ := by
    have := norm_pos_iff.2 hu
    positivity
  have hvn : (0 : ℝ) < ‖v‖⁻¹ := by
    have := norm_pos_iff.2 hv
    positivity
  have hU : ‖(‖u‖⁻¹ • u : E3)‖ = 1 := by
    rw [norm_smul]
    simp [norm_ne_zero_iff.2 hu]
  have hV : ‖(‖v‖⁻¹ • v : E3)‖ = 1 := by
    rw [norm_smul]
    simp [norm_ne_zero_iff.2 hv]
  have hset : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, u⟫ ∧ 0 ≤ ⟪x, v⟫}
      = {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, (‖u‖⁻¹ • u : E3)⟫ ∧ 0 ≤ ⟪x, (‖v‖⁻¹ • v : E3)⟫} := by
    ext x
    simp only [Set.mem_setOf_eq, real_inner_smul_right]
    constructor
    · rintro ⟨hn, ha, hb⟩
      exact ⟨hn, mul_nonneg hun.le ha, mul_nonneg hvn.le hb⟩
    · rintro ⟨hn, ha, hb⟩
      exact ⟨hn, nonneg_of_mul_nonneg_right ha hun, nonneg_of_mul_nonneg_right hb hvn⟩
  rw [hset, volume_wedge_unit _ _ hU hV, angle_smul_left_of_pos _ _ hun,
    angle_smul_right_of_pos _ _ hvn]

end Math

