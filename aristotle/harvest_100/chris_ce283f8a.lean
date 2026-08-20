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
def Hs (n : E3) : Set E3 := {x | 0 ≤ inner ℝ n x}

/-- The wedge: the part of the open unit ball where two linear forms are nonnegative. -/
def Wdg (u v : E3) : Set E3 := ball 0 1 ∩ Hs u ∩ Hs v

/-- The part of the open unit ball where three linear forms are nonnegative. -/
def Reg (u v w : E3) : Set E3 := Wdg u v ∩ Hs w

theorem measurableSet_Hs (n : E3) : MeasurableSet (Hs n) :=
  measurableSet_le measurable_const (by fun_prop)

theorem measurableSet_Wdg (u v : E3) : MeasurableSet (Wdg u v) :=
  (measurableSet_ball.inter (measurableSet_Hs u)).inter (measurableSet_Hs v)

theorem measurableSet_Reg (u v w : E3) : MeasurableSet (Reg u v w) :=
  (measurableSet_Wdg u v).inter (measurableSet_Hs w)

theorem Wdg_subset_ball (u v : E3) : Wdg u v ⊆ ball 0 1 := fun _ hx => hx.1.1

theorem Reg_subset_ball (u v w : E3) : Reg u v w ⊆ ball 0 1 := fun _ hx => hx.1.1.1

theorem volume_Wdg_ne_top (u v : E3) : volume (Wdg u v) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_ne_top (measure_mono (Wdg_subset_ball u v))

theorem volume_Reg_ne_top (u v w : E3) : volume (Reg u v w) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_ne_top (measure_mono (Reg_subset_ball u v w))

/-- A hyperplane through the origin is null. -/
theorem hyperplane_null {n : E3} (hn : n ≠ 0) : volume {x : E3 | inner ℝ n x = 0} = 0 := by
  have hset : {x : E3 | inner ℝ n x = 0} = ((ℝ ∙ n)ᗮ : Submodule ℝ E3) := by
    ext x
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : n ∈ (ℝ ∙ n)ᗮ := h ▸ Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact hn (inner_self_eq_zero.1 hmem)

/-- Splitting a measurable set by a hyperplane through the origin. -/
theorem volume_split {S : Set E3} (hS : MeasurableSet S) {n : E3} (hn : n ≠ 0) :
    volume S = volume (S ∩ Hs n) + volume (S ∩ Hs (-n)) := by
  have hmeas : MeasurableSet (S ∩ Hs (-n)) := hS.inter (measurableSet_Hs _)
  have hunion : (S ∩ Hs n) ∪ (S ∩ Hs (-n)) = S := by
    ext x
    simp only [Hs, mem_union, mem_inter_iff, mem_setOf_eq, inner_neg_left]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_total 0 (inner ℝ n x : ℝ) with hx | hx
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, by linarith⟩
  have hinter : volume ((S ∩ Hs n) ∩ (S ∩ Hs (-n))) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (hyperplane_null hn)
    obtain ⟨⟨-, h1⟩, -, h2⟩ := hx
    simp only [Hs, mem_setOf_eq, inner_neg_left] at h1 h2 ⊢
    linarith
  have hkey := measure_union_add_inter (μ := volume) (S ∩ Hs n) hmeas
  rw [hunion, hinter, add_zero] at hkey
  exact hkey

/-- The volume of a region is invariant under the antipodal map. -/
theorem volume_Reg_neg (u v w : E3) : volume (Reg (-u) (-v) (-w)) = volume (Reg u v w) := by
  have hpre : (⇑(LinearIsometryEquiv.neg ℝ (E := E3))) ⁻¹' (Reg (-u) (-v) (-w)) = Reg u v w := by
    ext x
    simp [Reg, Wdg, Hs, and_assoc]
  rw [← hpre]
  exact (((LinearIsometryEquiv.neg ℝ (E := E3)).measurePreserving).measure_preimage
    (measurableSet_Reg _ _ _).nullMeasurableSet).symm

theorem volume_Wdg (u v : E3) (hu : u ≠ 0) (hne : ∀ r : ℝ, v ≠ r • u) :
    volume (Wdg u v) = ENNReal.ofReal (2 / 3 * (π - angle u v)) :=
  wedge_volume u v hu hne

/-- **Girard's relation**. -/
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

theorem norm_lt_one_iff (x : E3) : ‖x‖ < 1 ↔ (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 < 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [show (1 : ℝ) = √1 by simp, Real.sqrt_lt_sqrt_iff (by positivity)]
  simp

/-- A measurable identification of `ℝ³` with `ℝ × (ℝ × ℝ)`, splitting off the last coordinate. -/
noncomputable def E3toProd : E3 → ℝ × (ℝ × ℝ) :=
  fun x => ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3) (WithLp.ofLp x))

theorem measurePreserving_E3toProd : MeasurePreserving E3toProd volume volume := by
  have h1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h3 : MeasurePreserving (fun q : ℝ × (Fin 2 → ℝ) =>
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow) q) volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  exact (h3.comp h2).comp h1

theorem E3toProd_apply (x : E3) : E3toProd x = (x 2, (x 0, x 1)) := by
  rfl

private theorem lintegral_one_sub_sq (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ (z : ℝ), ENNReal.ofReal (c * (1 - z ^ 2)) = ENNReal.ofReal (c * (4 / 3)) := by
  rw [← lintegral_add_compl (μ := volume) (fun z => ENNReal.ofReal (c * (1 - z ^ 2)))
      (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))]
  have h2 : ∫⁻ z in (Icc (-1 : ℝ) 1)ᶜ, ENNReal.ofReal (c * (1 - z ^ 2)) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Icc.compl
      (f := fun z => ENNReal.ofReal (c * (1 - z ^ 2))) (g := fun _ => 0) ?_, lintegral_zero]
    intro z hz
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hz
    have : 1 - z ^ 2 ≤ 0 := by rcases hz with h | h <;> nlinarith
    simp only [ENNReal.ofReal_eq_zero]
    nlinarith
  rw [h2, add_zero, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_pow 2)]
    simp [integral_pow]
    norm_num
  · apply Integrable.mono' (g := fun _ => c * 1) (integrable_const _)
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      simp only [mem_Icc] at hz
      have h0 : (0 : ℝ) ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc h0)]
      nlinarith
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    simp only [mem_Icc] at hz
    have h0 : (0 : ℝ) ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    exact mul_nonneg hc h0

/-- The volume of the wedge in standard position: the intersection of the unit ball with the
half-spaces `0 ≤ x 0` and `0 ≤ cos θ * x 0 + sin θ * x 1`. -/
theorem std_wedge_volume (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ < π) :
    volume {x : E3 | ‖x‖ < 1 ∧ 0 ≤ x 0 ∧ 0 ≤ cos θ * x 0 + sin θ * x 1}
      = ENNReal.ofReal (2 / 3 * (π - θ)) := by
  have hpi := Real.pi_pos
  set B : Set (ℝ × (ℝ × ℝ)) := {q : ℝ × (ℝ × ℝ) | q.2.1 ^ 2 + q.2.2 ^ 2 + q.1 ^ 2 < 1 ∧
    0 ≤ q.2.1 ∧ 0 ≤ cos θ * q.2.1 + sin θ * q.2.2} with hB
  have hBmeas : MeasurableSet B := by
    have : B = ({q : ℝ × (ℝ × ℝ) | q.2.1 ^ 2 + q.2.2 ^ 2 + q.1 ^ 2 < 1} ∩
        {q : ℝ × (ℝ × ℝ) | 0 ≤ q.2.1}) ∩
        {q : ℝ × (ℝ × ℝ) | 0 ≤ cos θ * q.2.1 + sin θ * q.2.2} := by
      ext q; simp [hB, and_assoc]
    rw [this]
    exact ((measurableSet_lt (by fun_prop) measurable_const).inter
      (measurableSet_le measurable_const (by fun_prop))).inter
      (measurableSet_le measurable_const (by fun_prop))
  have hpre : {x : E3 | ‖x‖ < 1 ∧ 0 ≤ x 0 ∧ 0 ≤ cos θ * x 0 + sin θ * x 1} = E3toProd ⁻¹' B := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, hB, E3toProd_apply]
    rw [norm_lt_one_iff]
  rw [hpre, measurePreserving_E3toProd.measure_preimage hBmeas.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hBmeas]
  have hslice : ∀ z : ℝ, volume (Prod.mk z ⁻¹' B) = ENNReal.ofReal ((π - θ) / 2 * (1 - z ^ 2)) := by
    intro z
    have : Prod.mk z ⁻¹' B = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1 - z ^ 2 ∧ 0 ≤ p.1 ∧
        0 ≤ cos θ * p.1 + sin θ * p.2} := by
      ext p
      simp only [hB, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
    rw [this, sector_area θ hθ0 hθπ]
  simp_rw [hslice]
  rw [lintegral_one_sub_sq _ (by linarith)]
  congr 1
  ring

/-- The volume of the intersection of the unit ball with two half-spaces through the origin,
with inner normals `u` and `v`: it is `2/3` times the dihedral angle `π - angle u v`. -/
theorem wedge_volume (u v : E3) (hu : u ≠ 0) (hne : ∀ r : ℝ, v ≠ r • u) :
    volume (ball (0 : E3) 1 ∩ {x | 0 ≤ inner ℝ u x} ∩ {x | 0 ≤ inner ℝ v x})
      = ENNReal.ofReal (2 / 3 * (π - InnerProductGeometry.angle u v)) := by
  have hv : v ≠ 0 := by simpa using hne 0
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu
  have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
  set θ := InnerProductGeometry.angle u v with hθ
  have hθ0 : 0 < θ := lt_of_le_of_ne (InnerProductGeometry.angle_nonneg u v) fun h => by
    obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h.symm
    exact hne r hr
  have hθπ : θ < π := lt_of_le_of_ne (InnerProductGeometry.angle_le_pi u v) fun h => by
    obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h
    exact hne r hr
  set e0 : E3 := ‖u‖⁻¹ • u with he0def
  have he0 : ‖e0‖ = 1 := by
    rw [he0def, norm_smul]; simp [inv_mul_cancel₀ (ne_of_gt hnu)]
  set c : ℝ := inner ℝ e0 v with hcdef
  have hc : c = ‖v‖ * cos θ := by
    rw [hcdef, he0def, real_inner_smul_left, hθ, InnerProductGeometry.cos_angle]
    field_simp
  set w : E3 := v - c • e0 with hwdef
  have hwnorm : ‖w‖ = ‖v‖ * sin θ := by
    have hsin : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le
    have h1 : ‖w‖ ^ 2 = ‖v‖ ^ 2 - c ^ 2 := by
      have h : (inner ℝ v e0 : ℝ) = c := by rw [real_inner_comm]
      rw [hwdef, norm_sub_sq_real, real_inner_smul_right, norm_smul, he0, h]
      simp only [Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have h2 : ‖v‖ ^ 2 - c ^ 2 = (‖v‖ * sin θ) ^ 2 := by
      rw [hc]
      have := Real.sin_sq_add_cos_sq θ
      nlinarith
    nlinarith [norm_nonneg w, mul_nonneg hnv.le hsin, h1, h2]
  have hwpos : (0 : ℝ) < ‖w‖ := by
    rw [hwnorm]; exact mul_pos hnv (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
  have hwne : w ≠ 0 := norm_pos_iff.1 hwpos
  set e1 : E3 := ‖w‖⁻¹ • w with he1def
  have he1 : ‖e1‖ = 1 := by
    rw [he1def, norm_smul]; simp [inv_mul_cancel₀ (ne_of_gt hwpos)]
  have h01 : inner ℝ e0 e1 = (0 : ℝ) := by
    rw [he1def, real_inner_smul_right, hwdef, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, he0]
    simp [hcdef]
  obtain ⟨b, hb0, hb1⟩ : ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e0 ∧ b 1 = e1 := by
    have horth : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![e0, e1, 0]) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      have h10 : inner ℝ e1 e0 = (0 : ℝ) := by rw [real_inner_comm]; exact h01
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp [Set.restrict, he0, he1, h01, h10, Subtype.ext_iff]
    obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
      (by simp : Module.finrank ℝ E3 = Fintype.card (Fin 3))
    exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp)⟩
  set R := b.repr with hR
  have hR0 : ∀ x : E3, (R x) 0 = ‖u‖⁻¹ * inner ℝ u x := by
    intro x
    rw [hR, OrthonormalBasis.repr_apply_apply, hb0, he0def, real_inner_smul_left]
  have hR1 : ∀ x : E3, (R x) 1 = ‖w‖⁻¹ * (inner ℝ v x - c * (inner ℝ e0 x)) := by
    intro x
    rw [hR, OrthonormalBasis.repr_apply_apply, hb1, he1def, real_inner_smul_left, hwdef,
      inner_sub_left, real_inner_smul_left]
  have hui : (0 : ℝ) < ‖u‖⁻¹ := inv_pos.2 hnu
  have hvi : (0 : ℝ) < ‖v‖⁻¹ := inv_pos.2 hnv
  have hpre : (ball (0 : E3) 1 ∩ {x | 0 ≤ inner ℝ u x} ∩ {x | 0 ≤ inner ℝ v x})
      = R ⁻¹' {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos θ * y 0 + sin θ * y 1} := by
    ext x
    have key : cos θ * (‖u‖⁻¹ * inner ℝ u x) +
        sin θ * (‖w‖⁻¹ * (inner ℝ v x - c * inner ℝ e0 x)) = ‖v‖⁻¹ * inner ℝ v x := by
      have hie0 : (inner ℝ e0 x : ℝ) = ‖u‖⁻¹ * inner ℝ u x := by
        rw [he0def, real_inner_smul_left]
      have hs : sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
      rw [hie0, hwnorm, hc]
      field_simp
      ring
    simp only [mem_inter_iff, mem_ball_zero_iff, mem_setOf_eq, mem_preimage,
      R.norm_map x, hR0 x, hR1 x, and_assoc, key, mul_nonneg_iff_of_pos_left hui,
      mul_nonneg_iff_of_pos_left hvi]
  have hAmeas : MeasurableSet {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos θ * y 0 + sin θ * y 1} := by
    have : {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos θ * y 0 + sin θ * y 1} =
        {y : E3 | ‖y‖ < 1} ∩ ({y : E3 | 0 ≤ y 0} ∩ {y : E3 | 0 ≤ cos θ * y 0 + sin θ * y 1}) := by
      ext y; simp
    rw [this]
    exact (measurableSet_lt (by fun_prop) measurable_const).inter
      ((measurableSet_le measurable_const (by fun_prop)).inter
        (measurableSet_le measurable_const (by fun_prop)))
  rw [hpre, (LinearIsometryEquiv.measurePreserving R).measure_preimage hAmeas.nullMeasurableSet,
    std_wedge_volume θ hθ0.le hθπ]

end Math

import Mathlib

/-!
# Area of a plane circular sector

This file computes the Lebesgue measure of a plane sector
`{p | ‖p‖² < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2}`, the intersection of a disc of
squared radius `s` with two half-planes whose bounding lines meet at an angle `π - θ`.
-/

open MeasureTheory Metric Set Real

namespace Math

/-- Characterisation of the angular sector cut out by two half planes. -/
theorem cos_nonneg_pair_iff (θ φ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ < π) (hφ : φ ∈ Ioo (-π) π) :
    (0 ≤ cos φ ∧ 0 ≤ cos θ * cos φ + sin θ * sin φ) ↔ φ ∈ Icc (θ - π / 2) (π / 2) := by
  have key : cos θ * cos φ + sin θ * sin φ = cos (φ - θ) := by rw [Real.cos_sub]; ring
  have hpi := Real.pi_pos
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩
    have hup : φ ≤ π / 2 := by
      by_contra h; push_neg at h
      exact absurd h1 (not_le.2 (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [hφ.2])))
    have hlo : -(π / 2) ≤ φ := by
      by_contra h; push_neg at h
      have : cos (-φ) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hφ.1])
      rw [Real.cos_neg] at this; linarith
    refine ⟨?_, hup⟩
    by_contra h
    push_neg at h
    have h3 : π / 2 < -(φ - θ) := by linarith
    have h4 : -(φ - θ) < π + π / 2 := by linarith
    have := Real.cos_neg_of_pi_div_two_lt_of_lt h3 h4
    rw [Real.cos_neg] at this; linarith
  · rintro ⟨h1, h2⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩

private theorem lintegral_ofReal_id_Ioo (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal x = ENNReal.ofReal (a ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha, integral_id]
    ring
  · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using le_of_lt hx.1

/-- The area of the sector of the disc of squared radius `s` cut out by the two half planes
`0 ≤ p.1` and `0 ≤ cos θ * p.1 + sin θ * p.2` is `(π - θ) / 2 * s`. -/
theorem sector_area (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ < π) (s : ℝ) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2}
      = ENNReal.ofReal ((π - θ) / 2 * s) := by
  have hpi := Real.pi_pos
  rcases le_or_gt s 0 with hs | hs
  · have hemp :
        {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2} = ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    rw [hemp, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
    nlinarith
  · set S : Set (ℝ × ℝ) :=
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2} with hS
    have hSmeas : MeasurableSet S := by
      have : S = ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s} ∩ {p : ℝ × ℝ | 0 ≤ p.1}) ∩
          {p : ℝ × ℝ | 0 ≤ cos θ * p.1 + sin θ * p.2} := by
        ext p; simp [hS, and_assoc]
      rw [this]
      exact ((measurableSet_lt (by fun_prop) measurable_const).inter
        (measurableSet_le measurable_const (by fun_prop))).inter
        (measurableSet_le measurable_const (by fun_prop))
    rw [← lintegral_indicator_one hSmeas, ← lintegral_comp_polarCoord_symm]
    have hmain : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator (1 : ℝ × ℝ → ENNReal) (polarCoord.symm p)
          = (Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)).indicator
              (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
      rintro ⟨r, φ⟩ hp
      obtain ⟨hr, hφ⟩ : r ∈ Ioi (0 : ℝ) ∧ φ ∈ Ioo (-π) π := hp
      have hr0 : 0 < r := hr
      have hiff : (polarCoord.symm (r, φ)) ∈ S ↔
          ((r, φ) ∈ Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)) := by
        rw [hS]
        simp only [polarCoord_symm_apply, mem_setOf_eq, mem_prod, mem_Ioo, mem_Icc]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨hr0, ?_⟩,
            (cos_nonneg_pair_iff θ φ hθ0 hθπ hφ).1 ⟨nonneg_of_mul_nonneg_right h2 hr0, ?_⟩⟩
          · have : r ^ 2 < s := by nlinarith [Real.sin_sq_add_cos_sq φ]
            nlinarith [Real.sq_sqrt hs.le, Real.sqrt_pos.2 hs, Real.sqrt_nonneg s]
          · nlinarith
        · rintro ⟨⟨-, h1⟩, h2⟩
          have hc := (cos_nonneg_pair_iff θ φ hθ0 hθπ hφ).2 h2
          refine ⟨?_, by nlinarith [hc.1], by nlinarith [hc.2]⟩
          have : r ^ 2 < s := by nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg s]
          nlinarith [Real.sin_sq_add_cos_sq φ]
      by_cases h : (polarCoord.symm (r, φ)) ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
        simp
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun hc => h (hiff.2 hc)]
        simp
    rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hmain]
    have hA : MeasurableSet (Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)) :=
      measurableSet_Ioo.prod measurableSet_Icc
    have hsub : (Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)) ⊆ polarCoord.target := by
      rintro ⟨r, φ⟩ ⟨h1, h2⟩
      exact ⟨h1.1, by simp only [mem_Icc] at h2; constructor <;> [linarith [h2.1]; linarith [h2.2]]⟩
    rw [lintegral_indicator hA, Measure.restrict_restrict hA, inter_eq_self_of_subset_left hsub,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Icc]
    rw [lintegral_mul_const' _ _ (by simp), lintegral_ofReal_id_Ioo _ (Real.sqrt_nonneg s),
      Real.sq_sqrt hs.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring_nf

end Math

/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The angle sum of a geodesic triangle on the unit sphere exceeds `π` by its area.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-! ### The cross product on `ℝ³` -/

/-- The cross product of two vectors of `ℝ³`. -/
noncomputable def cross (x y : E3) : E3 :=
  WithLp.toLp 2 ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

@[simp] theorem cross_apply0 (x y : E3) : (cross x y) 0 = x 1 * y 2 - x 2 * y 1 := rfl
@[simp] theorem cross_apply1 (x y : E3) : (cross x y) 1 = x 2 * y 0 - x 0 * y 2 := rfl
@[simp] theorem cross_apply2 (x y : E3) : (cross x y) 2 = x 0 * y 1 - x 1 * y 0 := rfl

theorem inner_three (x y : E3) : (inner ℝ x y : ℝ) = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The Binet–Cauchy identity. -/
theorem inner_cross_cross (x y z t : E3) : (inner ℝ (cross x y) (cross z t) : ℝ)
    = (inner ℝ x z) * (inner ℝ y t) - (inner ℝ x t) * (inner ℝ y z) := by
  simp only [inner_three, cross_apply0, cross_apply1, cross_apply2]; ring

theorem inner_cross_left (x y : E3) : (inner ℝ (cross x y) x : ℝ) = 0 := by
  simp only [inner_three, cross_apply0, cross_apply1, cross_apply2]; ring

theorem inner_cross_right (x y : E3) : (inner ℝ (cross x y) y : ℝ) = 0 := by
  simp only [inner_three, cross_apply0, cross_apply1, cross_apply2]; ring

/-- The scalar triple product is invariant under cyclic permutations. -/
theorem inner_cross_cyclic (x y z : E3) :
    (inner ℝ (cross x y) z : ℝ) = inner ℝ (cross y z) x := by
  simp only [inner_three, cross_apply0, cross_apply1, cross_apply2]; ring

/-! ### Spherical triangles and their angles -/

/-- The geodesic triangle on the unit sphere with vertices `a`, `b`, `c`: the set of unit
vectors that are nonnegative combinations of `a`, `b` and `c`. -/
def sphericalTriangle (a b c : E3) : Set (sphere (0 : E3) 1) :=
  {x | ∃ p q r : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r ∧ (x : E3) = p • a + q • b + r • c}

/-- The interior angle at the vertex `a` of the spherical triangle with vertices `a`, `b`, `c`:
the angle between the tangent directions at `a` pointing towards `b` and towards `c`. -/
noncomputable def sphAngle (a b c : E3) : ℝ :=
  angle (b - (inner ℝ a b : ℝ) • a) (c - (inner ℝ a c : ℝ) • a)

/-! ### Auxiliary lemmas -/

/-- Two angles are supplementary if the inner products are opposite and the norms agree. -/
theorem angle_eq_pi_sub_angle {x y z t : E3} (hnum : (inner ℝ x y : ℝ) = -inner ℝ z t)
    (h1 : ‖x‖ = ‖z‖) (h2 : ‖y‖ = ‖t‖) : angle x y = π - angle z t := by
  rw [angle, angle, hnum, h1, h2, neg_div, Real.arccos_neg]

/-- If `v` vanishes on `x` while `u` does not, and `v` is not zero, then `v` is not a multiple
of `u`. -/
theorem not_parallel_of_dual {u v x y : E3} {d : ℝ} (hd : d ≠ 0)
    (hux : (inner ℝ u x : ℝ) = d) (hvx : (inner ℝ v x : ℝ) = 0) (hvy : (inner ℝ v y : ℝ) = d) :
    ∀ r : ℝ, v ≠ r • u := by
  intro r hr
  have h0 : (0 : ℝ) = r * d := by rw [← hvx, hr, real_inner_smul_left, hux]
  have hr0 : r = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exact h
    · exact absurd h hd
  rw [hr0, zero_smul] at hr
  rw [hr] at hvy
  simp only [inner_zero_left] at hvy
  exact hd hvy.symm

theorem ne_zero_of_inner_ne_zero {u x : E3} {d : ℝ} (hd : d ≠ 0) (hux : (inner ℝ u x : ℝ) = d) :
    u ≠ 0 := by
  intro h
  rw [h] at hux
  simp only [inner_zero_left] at hux
  exact hd hux.symm

/-! ### The area of a spherical triangle in terms of the dual frame -/

section DualFrame

variable {a b c u v w : E3} {d : ℝ}

/-- Membership in the cone spanned by `a`, `b`, `c`, in terms of the dual frame. -/
theorem mem_cone_iff (hd : 0 < d)
    (hua : (inner ℝ u a : ℝ) = d) (hub : (inner ℝ u b : ℝ) = 0) (huc : (inner ℝ u c : ℝ) = 0)
    (hva : (inner ℝ v a : ℝ) = 0) (hvb : (inner ℝ v b : ℝ) = d) (hvc : (inner ℝ v c : ℝ) = 0)
    (hwa : (inner ℝ w a : ℝ) = 0) (hwb : (inner ℝ w b : ℝ) = 0) (hwc : (inner ℝ w c : ℝ) = d)
    (hspan : ∀ x : E3, ∃ p q r : ℝ, x = p • a + q • b + r • c) (x : E3) :
    (∃ p q r : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r ∧ x = p • a + q • b + r • c) ↔
      (0 ≤ (inner ℝ u x : ℝ) ∧ 0 ≤ (inner ℝ v x : ℝ) ∧ 0 ≤ (inner ℝ w x : ℝ)) := by
  have key : ∀ (n : E3) (na nb nc : ℝ), (inner ℝ n a : ℝ) = na → (inner ℝ n b : ℝ) = nb →
      (inner ℝ n c : ℝ) = nc → ∀ p q r : ℝ, (inner ℝ n (p • a + q • b + r • c) : ℝ)
        = p * na + q * nb + r * nc := by
    intro n na nb nc h1 h2 h3 p q r
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, h1, h2, h3]
  constructor
  · rintro ⟨p, q, r, hp, hq, hr, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [key u d 0 0 hua hub huc]; nlinarith
    · rw [key v 0 d 0 hva hvb hvc]; nlinarith
    · rw [key w 0 0 d hwa hwb hwc]; nlinarith
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨p, q, r, rfl⟩ := hspan x
    rw [key u d 0 0 hua hub huc] at h1
    rw [key v 0 d 0 hva hvb hvc] at h2
    rw [key w 0 0 d hwa hwb hwc] at h3
    exact ⟨p, q, r, by nlinarith, by nlinarith, by nlinarith, rfl⟩

/-- The cone over the spherical triangle, intersected with the unit ball, is the region
`Reg u v w` cut out by the dual frame. -/
theorem smul_triangle_eq (hd : 0 < d)
    (hua : (inner ℝ u a : ℝ) = d) (hub : (inner ℝ u b : ℝ) = 0) (huc : (inner ℝ u c : ℝ) = 0)
    (hva : (inner ℝ v a : ℝ) = 0) (hvb : (inner ℝ v b : ℝ) = d) (hvc : (inner ℝ v c : ℝ) = 0)
    (hwa : (inner ℝ w a : ℝ) = 0) (hwb : (inner ℝ w b : ℝ) = 0) (hwc : (inner ℝ w c : ℝ) = d)
    (hspan : ∀ x : E3, ∃ p q r : ℝ, x = p • a + q • b + r • c) :
    Ioo (0 : ℝ) 1 • ((↑) '' (sphericalTriangle a b c) : Set E3) = Reg u v w \ {0} := by
  have hcone := mem_cone_iff hd hua hub huc hva hvb hvc hwa hwb hwc hspan
  have hReg : ∀ z : E3, z ∈ Reg u v w ↔ (‖z‖ < 1 ∧ 0 ≤ (inner ℝ u z : ℝ) ∧
      0 ≤ (inner ℝ v z : ℝ) ∧ 0 ≤ (inner ℝ w z : ℝ)) := by
    intro z
    simp only [Reg, Wdg, Hs, mem_inter_iff, mem_ball_zero_iff, mem_setOf_eq, and_assoc]
  ext y
  constructor
  · rintro ⟨t, ht, x, hx, rfl⟩
    obtain ⟨x, hxs, rfl⟩ := hx
    have hxn : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
    have hmem := (hcone (x : E3)).1 hxs
    refine ⟨(hReg _).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [norm_smul, hxn, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
      exact ht.2
    · rw [real_inner_smul_right]; exact mul_nonneg ht.1.le hmem.1
    · rw [real_inner_smul_right]; exact mul_nonneg ht.1.le hmem.2.1
    · rw [real_inner_smul_right]; exact mul_nonneg ht.1.le hmem.2.2
    · simp only [mem_singleton_iff, smul_eq_zero, not_or]
      refine ⟨ne_of_gt ht.1, fun h => ?_⟩
      rw [h, norm_zero] at hxn
      exact zero_ne_one hxn
  · rintro ⟨hz, hy0'⟩
    obtain ⟨hyn1, hu, hv, hw⟩ := (hReg y).1 hz
    have hy0 : y ≠ 0 := by simpa using hy0'
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hsph : ‖y‖⁻¹ • y ∈ sphere (0 : E3) 1 := by
      simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hyn)]
    refine ⟨‖y‖, ⟨hyn, hyn1⟩, ‖y‖⁻¹ • y, ⟨⟨‖y‖⁻¹ • y, hsph⟩, ?_, rfl⟩, ?_⟩
    · refine (hcone _).2 ⟨?_, ?_, ?_⟩ <;> rw [real_inner_smul_right] <;>
        exact mul_nonneg (inv_pos.2 hyn).le (by assumption)
    · show ‖y‖ • (‖y‖⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hyn), one_smul]

/-- The area of the spherical triangle, computed with the cone measure on the sphere. -/
theorem area_eq_of_dualFrame (hd : 0 < d)
    (hua : (inner ℝ u a : ℝ) = d) (hub : (inner ℝ u b : ℝ) = 0) (huc : (inner ℝ u c : ℝ) = 0)
    (hva : (inner ℝ v a : ℝ) = 0) (hvb : (inner ℝ v b : ℝ) = d) (hvc : (inner ℝ v c : ℝ) = 0)
    (hwa : (inner ℝ w a : ℝ) = 0) (hwb : (inner ℝ w b : ℝ) = 0) (hwc : (inner ℝ w c : ℝ) = d)
    (hspan : ∀ x : E3, ∃ p q r : ℝ, x = p • a + q • b + r • c) :
    (volume.toSphere (sphericalTriangle a b c)).toReal
      = (π - angle v w) + (π - angle u w) + (π - angle u v) - π := by
  have hcone := mem_cone_iff hd hua hub huc hva hvb hvc hwa hwb hwc hspan
  have hTmeas : MeasurableSet (sphericalTriangle a b c) := by
    have : sphericalTriangle a b c
        = (Subtype.val : sphere (0 : E3) 1 → E3) ⁻¹' (Hs u ∩ Hs v ∩ Hs w) := by
      ext x
      simp only [sphericalTriangle, mem_setOf_eq, mem_preimage, mem_inter_iff, Hs, and_assoc]
      exact hcone (x : E3)
    rw [this]
    exact (measurable_subtype_coe
      (((measurableSet_Hs u).inter (measurableSet_Hs v)).inter (measurableSet_Hs w)))
  rw [Measure.toSphere_apply' _ hTmeas,
    smul_triangle_eq hd hua hub huc hva hvb hvc hwa hwb hwc hspan,
    measure_diff_null (measure_singleton 0)]
  rw [show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin]
  rw [ENNReal.toReal_mul]
  have hne : u ≠ 0 := ne_zero_of_inner_ne_zero (ne_of_gt hd) hua
  have hnv : v ≠ 0 := ne_zero_of_inner_ne_zero (ne_of_gt hd) hvb
  have huv : ∀ r : ℝ, v ≠ r • u := not_parallel_of_dual (ne_of_gt hd) hua hva hvb
  have huw : ∀ r : ℝ, w ≠ r • u := not_parallel_of_dual (ne_of_gt hd) hua hwa hwc
  have hvw : ∀ r : ℝ, w ≠ r • v := not_parallel_of_dual (ne_of_gt hd) hvb hwb hwc
  have := volume_Reg u v w hne hnv huv huw hvw
  simp only [ENNReal.toReal_natCast]
  push_cast
  linarith

end DualFrame


/-! ### The Gauss–Bonnet theorem for a spherical triangle -/

/-- `‖x × a‖ = ‖x - ⟪a,x⟫ a‖` for a unit vector `a`. -/
theorem norm_cross_right (a x : E3) (ha : ‖a‖ = 1) :
    ‖cross x a‖ = ‖x - (inner ℝ a x : ℝ) • a‖ := by
  have hsq : ‖cross x a‖ ^ 2 = ‖x - (inner ℝ a x : ℝ) • a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_cross_cross]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha,
      real_inner_comm a x]
    ring
  rw [show ‖cross x a‖ = √(‖cross x a‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, hsq,
    Real.sqrt_sq (norm_nonneg _)]

/-- `‖a × x‖ = ‖x - ⟪a,x⟫ a‖` for a unit vector `a`. -/
theorem norm_cross_left (a x : E3) (ha : ‖a‖ = 1) :
    ‖cross a x‖ = ‖x - (inner ℝ a x : ℝ) • a‖ := by
  have hsq : ‖cross a x‖ ^ 2 = ‖x - (inner ℝ a x : ℝ) • a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_cross_cross]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha,
      real_inner_comm a x]
    ring
  rw [show ‖cross a x‖ = √(‖cross a x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, hsq,
    Real.sqrt_sq (norm_nonneg _)]

/-- Three linearly independent vectors span `ℝ³`. -/
theorem span_of_linearIndependent {a b c : E3} (hli : LinearIndependent ℝ ![a, b, c]) (x : E3) :
    ∃ p q r : ℝ, x = p • a + q • b + r • c := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ⇑B = ![a, b, c] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨B.repr x 0, B.repr x 1, B.repr x 2, ?_⟩
  have hsum := B.sum_repr x
  rw [Fin.sum_univ_three, hB] at hsum
  simpa using hsum.symm

theorem not_parallel_of_linearIndependent {a b c : E3} (hli : LinearIndependent ℝ ![a, b, c]) :
    ∀ r : ℝ, c ≠ r • b := by
  intro r hr
  have h := Fintype.linearIndependent_iff.1 hli ![0, r, -1] (by simp [Fin.sum_univ_three, hr]) 2
  simp at h

/-- The scalar triple product of three linearly independent vectors is nonzero. -/
theorem triple_product_ne_zero {a b c : E3} (hb : ‖b‖ = 1)
    (hli : LinearIndependent ℝ ![a, b, c]) : (inner ℝ (cross b c) a : ℝ) ≠ 0 := by
  intro hD
  -- the cross product is orthogonal to a spanning family, hence zero
  obtain ⟨p, q, r, hx⟩ := span_of_linearIndependent hli (cross b c)
  have hzero : (inner ℝ (cross b c) (cross b c) : ℝ) = 0 := by
    nth_rewrite 2 [hx]
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hD, inner_cross_left, inner_cross_right]
    ring
  have hcross : cross b c = 0 := inner_self_eq_zero.1 hzero
  -- hence `b` and `c` are parallel
  have hnorm : ‖c - (inner ℝ b c : ℝ) • b‖ = 0 := by
    rw [← norm_cross_left b c hb, hcross, norm_zero]
  have : c = (inner ℝ b c : ℝ) • b := by
    have := norm_eq_zero.1 hnorm
    linear_combination (norm := module) this
  exact not_parallel_of_linearIndependent hli _ this

/-- **Gauss–Bonnet for a spherical triangle** (Girard's theorem): the area of a geodesic
triangle on the unit sphere, measured with the canonical (cone) measure on the sphere,
equals the sum of its three interior angles minus `π`. -/
theorem gauss_bonnet_polygon (a b c : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hli : LinearIndependent ℝ ![a, b, c]) :
    (volume.toSphere (sphericalTriangle a b c)).toReal
      = sphAngle a b c + sphAngle b a c + sphAngle c a b - π := by
  have haa : (inner ℝ a a : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : (inner ℝ b b : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have hcc : (inner ℝ c c : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hc]; norm_num
  set D : ℝ := inner ℝ (cross b c) a with hDdef
  have hD : D ≠ 0 := triple_product_ne_zero hb hli
  set ε : ℝ := if 0 < D then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by rw [hεdef]; split <;> simp
  have hd : 0 < ε * D := by
    rw [hεdef]
    split <;> rename_i h
    · simpa using h
    · push_neg at h
      have : D < 0 := lt_of_le_of_ne h hD
      nlinarith
  -- the dual frame
  have hca : (inner ℝ (cross c a) b : ℝ) = D := by
    rw [inner_cross_cyclic c a b, inner_cross_cyclic a b c]
  have hab : (inner ℝ (cross a b) c : ℝ) = D := inner_cross_cyclic a b c
  have hua : (inner ℝ (ε • cross b c) a : ℝ) = ε * D := by rw [real_inner_smul_left]
  have hub : (inner ℝ (ε • cross b c) b : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_cross_left]; ring
  have huc : (inner ℝ (ε • cross b c) c : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_cross_right]; ring
  have hva : (inner ℝ (ε • cross c a) a : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_cross_right]; ring
  have hvb : (inner ℝ (ε • cross c a) b : ℝ) = ε * D := by rw [real_inner_smul_left, hca]
  have hvc : (inner ℝ (ε • cross c a) c : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_cross_left]; ring
  have hwa : (inner ℝ (ε • cross a b) a : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_cross_left]; ring
  have hwb : (inner ℝ (ε • cross a b) b : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_cross_right]; ring
  have hwc : (inner ℝ (ε • cross a b) c : ℝ) = ε * D := by rw [real_inner_smul_left, hab]
  have har := area_eq_of_dualFrame hd hua hub huc hva hvb hvc hwa hwb hwc
    (span_of_linearIndependent hli)
  -- the angles between the face normals are supplementary to the interior angles
  have hangle_smul : ∀ x y : E3, angle (ε • x) (ε • y) = angle x y := by
    intro x y
    rcases hε with h | h <;> simp [h, angle_neg_neg]
  have h1 : angle (ε • cross c a) (ε • cross a b) = π - sphAngle a b c := by
    have hnum : (inner ℝ (cross c a) (cross a b) : ℝ)
        = -inner ℝ (c - (inner ℝ a c : ℝ) • a) (b - (inner ℝ a b : ℝ) • a) := by
      simp only [inner_cross_cross, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, haa, real_inner_comm a c]
      ring
    rw [hangle_smul,
      angle_eq_pi_sub_angle hnum (norm_cross_right a c ha) (norm_cross_left a b ha),
      sphAngle, angle_comm]
  have h2 : angle (ε • cross b c) (ε • cross a b) = π - sphAngle b a c := by
    have hnum : (inner ℝ (cross b c) (cross a b) : ℝ)
        = -inner ℝ (c - (inner ℝ b c : ℝ) • b) (a - (inner ℝ b a : ℝ) • b) := by
      simp only [inner_cross_cross, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hbb, real_inner_comm b c]
      ring
    rw [hangle_smul,
      angle_eq_pi_sub_angle hnum (norm_cross_left b c hb) (norm_cross_right b a hb),
      sphAngle, angle_comm]
  have h3 : angle (ε • cross b c) (ε • cross c a) = π - sphAngle c a b := by
    have hnum : (inner ℝ (cross b c) (cross c a) : ℝ)
        = -inner ℝ (b - (inner ℝ c b : ℝ) • c) (a - (inner ℝ c a : ℝ) • c) := by
      simp only [inner_cross_cross, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hcc, real_inner_comm c b]
      ring
    rw [hangle_smul,
      angle_eq_pi_sub_angle hnum (norm_cross_right c b hc) (norm_cross_left c a hc),
      sphAngle, angle_comm]
  rw [har, h1, h2, h3]
  ring

/-! ### Consistency checks

Two sanity checks on the normalisation: the total area of the unit sphere is `4 * π`, and the
area of a spherical octant is `π / 2` (an eighth of `4 * π`), as predicted by the theorem above.
-/

/-- The volume of the unit ball of `ℝ³` is `4/3 * π`. -/
theorem volume_unit_ball : (volume (ball (0 : E3) 1)) = ENNReal.ofReal (4 / 3 * π) := by
  have h : Real.Gamma (3 / 2 + 1) = 3 / 4 * √π := by
    rw [Real.Gamma_add_one (by norm_num), show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, Nat.cast_ofNat, h]
  rw [show (√π) ^ 3 / (3 / 4 * √π) = 4 / 3 * (√π * √π) by
      field_simp [Real.sqrt_ne_zero'.2 Real.pi_pos],
    Real.mul_self_sqrt Real.pi_pos.le]
  simp

/-- The total area of the unit sphere in `ℝ³` is `4 * π`. -/
theorem sphere_area : (volume.toSphere (univ : Set (sphere (0 : E3) 1))).toReal = 4 * π := by
  rw [Measure.toSphere_apply_univ, volume_unit_ball,
    show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp
  ring

/-- The area of the spherical octant spanned by the three standard basis vectors is `π / 2`,
one eighth of the area of the sphere. -/
theorem octant_area :
    (volume.toSphere (sphericalTriangle (EuclideanSpace.single 0 (1 : ℝ))
      (EuclideanSpace.single 1 (1 : ℝ)) (EuclideanSpace.single 2 (1 : ℝ)))).toReal = π / 2 := by
  set e0 : E3 := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e1 : E3 := EuclideanSpace.single 1 (1 : ℝ) with he1
  set e2 : E3 := EuclideanSpace.single 2 (1 : ℝ) with he2
  have hinner : ∀ i j : Fin 3, (inner ℝ (EuclideanSpace.single i (1 : ℝ) : E3)
      (EuclideanSpace.single j (1 : ℝ)) : ℝ) = if i = j then 1 else 0 := by
    intro i j
    simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  have hnorm : ∀ i : Fin 3, ‖(EuclideanSpace.single i (1 : ℝ) : E3)‖ = 1 := by
    intro i; simp
  have hli : LinearIndependent ℝ ![e0, e1, e2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hcoord := congrFun (congrArg WithLp.ofLp hg) i
    simp [he0, he1, he2, Fin.sum_univ_three, EuclideanSpace.single_apply] at hcoord
    fin_cases i <;> simp_all
  have key : ∀ x y z : E3, (inner ℝ x y : ℝ) = 0 → (inner ℝ x z : ℝ) = 0 →
      (inner ℝ y z : ℝ) = 0 → sphAngle x y z = π / 2 := by
    intro x y z h1 h2 h3
    rw [sphAngle, h1, h2]
    simp only [zero_smul, sub_zero]
    exact (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two y z).1 h3
  rw [gauss_bonnet_polygon e0 e1 e2 (hnorm 0) (hnorm 1) (hnorm 2) hli,
    key e0 e1 e2 (by simp [he0, he1, hinner]) (by simp [he0, he2, hinner])
      (by simp [he1, he2, hinner]),
    key e1 e0 e2 (by simp [he0, he1, hinner]) (by simp [he1, he2, hinner])
      (by simp [he0, he2, hinner]),
    key e2 e0 e1 (by simp [he0, he2, hinner]) (by simp [he1, he2, hinner])
      (by simp [he0, he1, hinner])]
  ring

end Math

