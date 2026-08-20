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
noncomputable def cross (x y : E3) : E3 :=
  !₂[x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

/-- The interior angle at the vertex `x` of the geodesic triangle with vertices `x`, `y`, `z`
on the unit sphere: the angle between the initial directions of the two geodesics leaving `x`. -/
noncomputable def sphAngle (x y z : E3) : ℝ :=
  InnerProductGeometry.angle (y - ⟪x, y⟫ • x) (z - ⟪x, z⟫ • x)

/-- The (closed) geodesic triangle on the unit sphere with vertices `a`, `b`, `c`: the part of
the sphere lying in the convex cone spanned by `a`, `b`, `c`. -/
def sphTriangle (a b c : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ x = α • a + β • b + γ • c}

/-- The spherical area of a subset of the unit sphere, defined - exactly as Mathlib's spherical
measure `MeasureTheory.Measure.toSphere` - as `3 = dim ℝ³` times the volume of the cone
`{t • x : 0 < t < 1, x ∈ S}` over `S`. -/
noncomputable def sphArea (S : Set E3) : ℝ := 3 * (volume (Set.Ioo (0:ℝ) 1 • S)).toReal

/-- The open half-ball cut out by the vector `u`; the cone over an open hemisphere. -/
def hemiCone (u : E3) : Set E3 := {x : E3 | ‖x‖ < 1 ∧ 0 < ⟪u, x⟫}

/-- `sphArea` agrees with Mathlib's spherical measure `Measure.toSphere`. -/
theorem sphArea_eq_toSphere (S : Set (sphere (0 : E3) 1)) (hS : MeasurableSet S) :
    sphArea (Subtype.val '' S) = ((volume : Measure E3).toSphere S).toReal := by
  rw [Measure.toSphere_apply' _ hS, ENNReal.toReal_mul, sphArea]
  norm_num

/-! ### Basic facts about the cross product -/

theorem inner_cross_cross (x y z w : E3) :
    ⟪cross x y, cross z w⟫ = ⟪x, z⟫ * ⟪y, w⟫ - ⟪x, w⟫ * ⟪y, z⟫ := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_left (x y : E3) : ⟪cross x y, x⟫ = 0 := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_right (x y : E3) : ⟪cross x y, y⟫ = 0 := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_rotate (x y z : E3) : ⟪x, cross y z⟫ = ⟪y, cross z x⟫ := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem cross_swap (x y : E3) : cross x y = - cross y x := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

theorem inner_cross_ne_zero_of_linearIndependent {a b c : E3}
    (h : LinearIndependent ℝ ![a, b, c]) : ⟪a, cross b c⟫ ≠ 0 := by
  set M : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of ![(a : Fin 3 → ℝ), (b : Fin 3 → ℝ), (c : Fin 3 → ℝ)] with hM
  have hrow : LinearIndependent ℝ M.row := by
    have hr : M.row = fun i => ((EuclideanSpace.equiv (Fin 3) ℝ) (![a, b, c] i)) := by
      funext i
      fin_cases i <;> rfl
    rw [hr]
    exact h.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap (by simp [LinearEquiv.ker])
  have hdet : M.det ≠ 0 := by
    have hU := Matrix.linearIndependent_rows_iff_isUnit.mp hrow
    rw [Matrix.isUnit_iff_isUnit_det] at hU
    exact hU.ne_zero
  have hEq : ⟪a, cross b c⟫ = M.det := by
    simp [hM, cross, PiLp.inner_apply, Fin.sum_univ_three, Matrix.det_fin_three]; ring
  rw [hEq]; exact hdet

/-! ### The angle at a vertex in terms of the normals of the sides -/

/-- The interior angle at the vertex `a` is `π` minus the angle between the two outer normals
of the sides through `a`. -/
theorem norm_cross_right (a x : E3) (ha : ‖a‖ = 1) : ‖cross x a‖ = ‖x - ⟪a, x⟫ • a‖ := by
  have h1 : ‖cross x a‖ ^ 2 = ‖x - ⟪a, x⟫ • a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_cross_cross, norm_sub_sq_real, norm_smul,
      real_inner_smul_right, real_inner_comm x a, ha]
    simp [ha]
    ring
  nlinarith [norm_nonneg (cross x a), norm_nonneg (x - ⟪a, x⟫ • a), h1]

theorem sphAngle_eq_pi_sub (a b c : E3) (ha : ‖a‖ = 1) :
    sphAngle a b c = π - InnerProductGeometry.angle (cross c a) (cross a b) := by
  have h1 : ‖cross c a‖ = ‖c - ⟪a, c⟫ • a‖ := norm_cross_right a c ha
  have h2 : ‖cross a b‖ = ‖b - ⟪a, b⟫ • a‖ := by
    rw [cross_swap a b, norm_neg]; exact norm_cross_right a b ha
  have h3 : ⟪cross c a, cross a b⟫ = - ⟪b - ⟪a, b⟫ • a, c - ⟪a, c⟫ • a⟫ := by
    rw [inner_cross_cross]
    simp [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, ha,
      real_inner_comm a b, real_inner_comm a c, real_inner_comm c b]
    ring
  unfold sphAngle InnerProductGeometry.angle
  rw [h1, h2, h3, ← Real.arccos_neg]
  congr 1
  rw [real_inner_comm]
  ring

/-! ### Volumes -/

theorem measure_union_null_right {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    (h : μ t = 0) : μ (s ∪ t) = μ s :=
  le_antisymm (le_trans (measure_union_le s t) (by rw [h, add_zero]))
    (measure_mono Set.subset_union_left)

theorem isOpen_hemiCone (u : E3) : IsOpen (hemiCone u) := by
  have h1 : IsOpen {x : E3 | ‖x‖ < 1} := isOpen_lt continuous_norm continuous_const
  have h2 : IsOpen {x : E3 | 0 < ⟪u, x⟫} := isOpen_lt continuous_const (by fun_prop)
  exact h1.inter h2

theorem measurableSet_hemiCone (u : E3) : MeasurableSet (hemiCone u) :=
  (isOpen_hemiCone u).measurableSet

theorem volume_inner_eq_zero {u : E3} (hu : u ≠ 0) : volume {x : E3 | ⟪u, x⟫ = 0} = 0 := by
  have hset : {x : E3 | ⟪u, x⟫ = 0} = (LinearMap.ker (innerSL ℝ u).toLinearMap : Submodule ℝ E3) := by
    ext x; simp [LinearMap.mem_ker]
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : u ∈ LinearMap.ker (innerSL ℝ u).toLinearMap := by rw [h]; trivial
  simp [LinearMap.mem_ker] at hmem
  exact hu hmem

/-- Splitting a set by the hyperplane orthogonal to `u`. -/
theorem volume_split (S : Set E3) (hS : MeasurableSet S) {u : E3} (hu : u ≠ 0) :
    volume S = volume (S ∩ {x | 0 < ⟪u, x⟫}) + volume (S ∩ {x | 0 < ⟪-u, x⟫}) := by
  have hZ : volume (S ∩ {x : E3 | ⟪u, x⟫ = 0}) = 0 :=
    measure_mono_null inter_subset_right (volume_inner_eq_zero hu)
  have hsplit : S = (S ∩ {x : E3 | 0 < ⟪u, x⟫}) ∪ (S ∩ {x : E3 | 0 < ⟪-u, x⟫})
      ∪ (S ∩ {x : E3 | ⟪u, x⟫ = 0}) := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_setOf_eq, inner_neg_left]
    constructor
    · intro hx
      rcases lt_trichotomy 0 ⟪u, x⟫ with h | h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h.symm⟩
      · exact Or.inl (Or.inr ⟨hx, by linarith⟩)
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have hmn : MeasurableSet (S ∩ {x : E3 | 0 < ⟪-u, x⟫}) :=
    hS.inter (measurableSet_lt measurable_const (by fun_prop))
  conv_lhs => rw [hsplit]
  rw [measure_union_null_right hZ]
  refine measure_union ?_ hmn
  rw [Set.disjoint_left]
  rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
  simp only [Set.mem_setOf_eq, inner_neg_left] at hx1 hx2
  linarith

theorem volume_unitBall : volume {x : E3 | ‖x‖ < 1} = ENNReal.ofReal (4 * π / 3) := by
  have h : {x : E3 | ‖x‖ < 1} = ball (0 : E3) 1 := by ext x; simp [mem_ball, dist_eq_norm]
  rw [h, EuclideanSpace.volume_ball]
  have hg : Real.Gamma ((3:ℝ)/2 + 1) = 3/4 * √π := by
    rw [Real.Gamma_add_one (by norm_num), show (3:ℝ)/2 = 1/2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  simp only [Fintype.card_fin]
  rw [show ((3:ℕ):ℝ)/2 + 1 = (3:ℝ)/2 + 1 by norm_num, hg]
  have hpi : √π ^ 3 = π * √π := by
    rw [show (3:ℕ) = 2 + 1 by rfl, pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [hpi, show π * √π / (3 / 4 * √π) = 4 * π / 3 by
    have : √π ≠ 0 := by positivity
    field_simp]
  simp

theorem volume_hemiCone {u : E3} (hu : u ≠ 0) :
    volume (hemiCone u) = ENNReal.ofReal (2 * π / 3) := by
  have hb : MeasurableSet {x : E3 | ‖x‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have h1 : {x : E3 | ‖x‖ < 1} ∩ {x | 0 < ⟪u, x⟫} = hemiCone u := rfl
  have h2 : {x : E3 | ‖x‖ < 1} ∩ {x | 0 < ⟪-u, x⟫} = hemiCone (-u) := rfl
  have hneg : hemiCone (-u) = -(hemiCone u) := by
    ext x; simp [hemiCone, inner_neg_left, inner_neg_right]
  have key := volume_split {x : E3 | ‖x‖ < 1} hb hu
  rw [h1, h2, hneg, Measure.measure_neg, volume_unitBall, ← two_mul] at key
  have h4 : ENNReal.ofReal (4 * π / 3) = 2 * ENNReal.ofReal (2 * π / 3) := by
    rw [show (4:ℝ) * π / 3 = 2 * (2 * π / 3) by ring, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [h4] at key
  exact ((ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp key).symm

/-! ### The area of a planar sector, by polar coordinates -/

/-- Description of the sector `{cos φ > 0} ∩ {cos (φ - θ) > 0}` as an interval of angles. -/
theorem sector_angle_iff (θ : ℝ) (h0 : 0 < θ) (hpi : θ < π) (φ : ℝ) (hφ : φ ∈ Ioo (-π) π) :
    (0 < Real.cos φ ∧ 0 < Real.cos (φ - θ)) ↔ (θ - π/2 < φ ∧ φ < π/2) := by
  obtain ⟨h1, h2⟩ := hφ
  constructor
  · rintro ⟨hc1, hc2⟩
    have hlt : φ < π/2 := by
      by_contra h
      push_neg at h
      have : Real.cos φ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
      linarith
    have hgt : -(π/2) < φ := by
      by_contra h
      push_neg at h
      have : Real.cos φ ≤ 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      linarith
    refine ⟨?_, hlt⟩
    by_contra h
    push_neg at h
    have : Real.cos (φ - θ) ≤ 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    linarith
  · rintro ⟨ha, hb⟩
    exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, hb⟩,
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩⟩

theorem lintegral_id_Ioo (r : ℝ) (hr : 0 < r) :
    ∫⁻ x in Ioo (0:ℝ) r, ENNReal.ofReal x = ENNReal.ofReal (r^2/2) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    simp [integral_id]
  · exact (intervalIntegral.intervalIntegrable_id (μ := volume) (a := 0) (b := r)).1.mono_set
      Ioo_subset_Ioc_self
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx using hx.1.le

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
theorem volume_sector (θ : ℝ) (h0 : 0 < θ) (hpi : θ < π) (R : ℝ) :
    volume {p : ℝ × ℝ | p.1^2 + p.2^2 < R ∧ 0 < p.1 ∧ 0 < Real.cos θ * p.1 + Real.sin θ * p.2}
      = ENNReal.ofReal ((π - θ)/2 * R) := by
  rcases le_or_gt R 0 with hR | hR
  · have hempty : {p : ℝ × ℝ | p.1^2 + p.2^2 < R ∧ 0 < p.1
        ∧ 0 < Real.cos θ * p.1 + Real.sin θ * p.2} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hd
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    rw [hempty, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
    have : 0 < (π - θ)/2 := by linarith
    nlinarith
  set S := {p : ℝ × ℝ | p.1^2 + p.2^2 < R ∧ 0 < p.1 ∧ 0 < Real.cos θ * p.1 + Real.sin θ * p.2}
    with hS
  have hSo : IsOpen S := by
    have h1 : IsOpen {p : ℝ × ℝ | p.1^2 + p.2^2 < R} := isOpen_lt (by fun_prop) continuous_const
    have h2 : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const (by fun_prop)
    have h3 : IsOpen {p : ℝ × ℝ | 0 < Real.cos θ * p.1 + Real.sin θ * p.2} :=
      isOpen_lt continuous_const (by fun_prop)
    exact h1.inter (h2.inter h3)
  have hSm : MeasurableSet S := hSo.measurableSet
  set r := Real.sqrt R with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hR
  have hrR : r^2 = R := Real.sq_sqrt hR.le
  set A := Ioo (0:ℝ) r ×ˢ Ioo (θ - π/2) (π/2) with hA
  have hAm : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioo
  have hAsub : A ⊆ polarCoord.target := by
    rintro ⟨ρ, φ⟩ ⟨h1, h2⟩
    refine ⟨h1.1, ?_, ?_⟩
    · simp only [] at h2 ⊢; linarith [h2.1, Real.pi_pos]
    · simp only [] at h2 ⊢; linarith [h2.2, Real.pi_pos]
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (polarCoord.symm p)
        = A.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
    rintro ⟨ρ, φ⟩ ⟨hρ, hφ⟩
    simp only [mem_Ioi] at hρ
    rw [polarCoord_symm_apply]
    have hpyth : (ρ * Real.cos φ)^2 + (ρ * Real.sin φ)^2 = ρ^2 := by
      have := Real.sin_sq_add_cos_sq φ; nlinarith
    have hcomb : Real.cos θ * (ρ * Real.cos φ) + Real.sin θ * (ρ * Real.sin φ)
        = ρ * Real.cos (φ - θ) := by rw [Real.cos_sub]; ring
    have hiff := sector_angle_iff θ h0 hpi φ hφ
    have hmem : ((ρ * Real.cos φ, ρ * Real.sin φ) ∈ S) ↔ ((ρ, φ) ∈ A) := by
      simp only [hS, hA, mem_setOf_eq, Set.mem_prod, mem_Ioo, hpyth, hcomb]
      constructor
      · rintro ⟨hd, hx, hy⟩
        have hc1 : 0 < Real.cos φ := by nlinarith
        have hc2 : 0 < Real.cos (φ - θ) := by nlinarith
        obtain ⟨hb1, hb2⟩ := hiff.mp ⟨hc1, hc2⟩
        exact ⟨⟨hρ, by nlinarith⟩, hb1, hb2⟩
      · rintro ⟨⟨-, hρr⟩, hb1, hb2⟩
        obtain ⟨hc1, hc2⟩ := hiff.mpr ⟨hb1, hb2⟩
        exact ⟨by nlinarith, by positivity, by positivity⟩
    by_cases hin : (ρ, φ) ∈ A
    · rw [Set.indicator_of_mem (hmem.mpr hin), Set.indicator_of_mem hin]
      simp
    · rw [Set.indicator_of_notMem (fun h => hin (hmem.mp h)), Set.indicator_of_notMem hin]
      simp
  rw [← lintegral_indicator_one hSm, ← lintegral_comp_polarCoord_symm (S.indicator 1),
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
    lintegral_indicator hAm, Measure.restrict_restrict hAm,
    Set.inter_eq_self_of_subset_left hAsub,
    lintegral_id_prod r _ _ hr0, hrR]
  congr 1
  ring

/-- The volume of the wedge of the unit ball of `ℝ × ℝ × ℝ` cut out by the two half-spaces
`{y > 0}` and `{cos θ · y + sin θ · z > 0}`, obtained by integrating the planar sector areas. -/
theorem volume_wedge3 (θ : ℝ) (h0 : 0 < θ) (hpi : θ < π) :
    volume {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
      0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} = ENNReal.ofReal (2 * (π - θ) / 3) := by
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
  rw [Measure.volume_eq_prod, Measure.prod_apply hTo.measurableSet]
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' {q : ℝ × (ℝ × ℝ) |
      q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
      0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2})
      = ENNReal.ofReal ((π - θ)/2 * (1 - t^2)) := by
    intro t
    have hs : (Prod.mk t ⁻¹' {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
        0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2})
        = {p : ℝ × ℝ | p.1^2 + p.2^2 < 1 - t^2 ∧ 0 < p.1 ∧
            0 < Real.cos θ * p.1 + Real.sin θ * p.2} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
    rw [hs, volume_sector θ h0 hpi]
  simp_rw [hslice]
  rw [← lintegral_add_compl _ (measurableSet_Ioo (a := (-1:ℝ)) (b := 1))]
  have hcompl : ∫⁻ t in (Ioo (-1:ℝ) 1)ᶜ, ENNReal.ofReal ((π - θ)/2 * (1 - t^2)) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioo.compl
      (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
    intro t ht
    have ht2 : 1 ≤ t^2 := by
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with h | h <;> nlinarith
    have hnn : (π - θ)/2 ≥ 0 := by linarith
    simp only [ENNReal.ofReal_eq_zero]
    nlinarith
  rw [hcompl, add_zero]
  have hint : IntegrableOn (fun t : ℝ => (π - θ)/2 * (1 - t^2)) (Ioo (-1:ℝ) 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (-1:ℝ) 1)] fun t : ℝ => (π - θ)/2 * (1 - t^2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    obtain ⟨h1, h2⟩ := ht
    have h3 : (0:ℝ) ≤ (π - θ)/2 := by linarith
    have h4 : (0:ℝ) ≤ 1 - t^2 := by nlinarith
    simpa using mul_nonneg h3 h4
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 2)]
  simp [integral_pow]
  ring

/-- The volume of the standard wedge of the unit ball of `ℝ³`, cut out by the half-spaces
`{y 1 > 0}` and `{cos θ · y 1 + sin θ · y 2 > 0}`. -/
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
theorem volume_lune {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h1 : u ≠ v) (h2 : u ≠ -v) :
    volume (hemiCone u ∩ hemiCone v) =
      ENNReal.ofReal (2 * (π - InnerProductGeometry.angle u v) / 3) := by
  set θ := InnerProductGeometry.angle u v with hθ
  have hcos : Real.cos θ = ⟪u, v⟫ := by
    rw [hθ, InnerProductGeometry.cos_angle, hu, hv]; norm_num
  have h0 : 0 < θ := by
    rcases lt_or_eq_of_le (InnerProductGeometry.angle_nonneg u v) with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hrv⟩ := (InnerProductGeometry.angle_eq_zero_iff (x := u) (y := v)).mp h.symm
      have hr1 : r = 1 := by
        have : ‖v‖ = r * ‖u‖ := by rw [hrv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        rw [hu, hv] at this; linarith
      exact h1 (by rw [hrv, hr1, one_smul])
  have hpi : θ < π := by
    rcases lt_or_eq_of_le (InnerProductGeometry.angle_le_pi u v) with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hrv⟩ := (InnerProductGeometry.angle_eq_pi_iff (x := u) (y := v)).mp h
      have hr1 : r = -1 := by
        have : ‖v‖ = |r| * ‖u‖ := by rw [hrv, norm_smul, Real.norm_eq_abs]
        rw [hu, hv, abs_of_neg hr] at this; linarith
      exact h2 (by rw [hrv, hr1]; module)
  have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  set e3 : E3 := (Real.sin θ)⁻¹ • (v - ⟪u, v⟫ • u) with he3def
  have hnormv : ‖v - ⟪u, v⟫ • u‖^2 = Real.sin θ ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq θ
    have hc : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm u v
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, hv, Real.norm_eq_abs, mul_one,
      sq_abs, hc, ← hcos]
    nlinarith
  have hne3 : ‖e3‖ = 1 := by
    rw [he3def, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (Real.sin θ)⁻¹)]
    have hnv : ‖v - ⟪u, v⟫ • u‖ = Real.sin θ := by
      nlinarith [norm_nonneg (v - ⟪u, v⟫ • u), hnormv]
    rw [hnv, inv_mul_cancel₀ hs0.ne']
  have hue3 : ⟪u, e3⟫ = 0 := by
    rw [he3def, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    ring
  have he3u : ⟪e3, u⟫ = 0 := by rw [real_inner_comm]; exact hue3
  have hvdecomp : v = Real.cos θ • u + Real.sin θ • e3 := by
    rw [he3def, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, hcos]
    module
  set e1 : E3 := cross u e3 with he1def
  have hne1 : ‖e1‖ = 1 := by
    rw [he1def, norm_cross_right e3 u hne3, he3u]
    simp [hu]
  have hi1 : ⟪e1, u⟫ = 0 := inner_cross_left u e3
  have hi2 : ⟪e1, e3⟫ = 0 := inner_cross_right u e3
  have hi1' : ⟪u, e1⟫ = 0 := by rw [real_inner_comm]; exact hi1
  have hi2' : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hi2
  have horth : Orthonormal ℝ ![e1, u, e3] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hne1, hu, hne3, hi1, hi2, hi1', hi2', hue3, he3u]
  obtain ⟨B, hB⟩ : ∃ B : OrthonormalBasis (Fin 3) ℝ E3, ∀ i, B i = ![e1, u, e3] i := by
    refine ⟨(basisOfLinearIndependentOfCardEqFinrank horth.linearIndependent
      (by simp)).toOrthonormalBasis ?_, ?_⟩
    · simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using horth
    · intro i; simp [Basis.coe_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hR := B.measurePreserving_repr
  have hW : IsOpen {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2} := by
    have hset : {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2}
        = ({y : E3 | ‖y‖ < 1} ∩ {y : E3 | 0 < y 1})
          ∩ {y : E3 | 0 < Real.cos θ * y 1 + Real.sin θ * y 2} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hpre : hemiCone u ∩ hemiCone v = B.repr ⁻¹'
      {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2} := by
    ext x
    have h1x : (B.repr x) 1 = ⟪u, x⟫ := by
      rw [B.repr_apply_apply, hB 1]; simp
    have h2x : (B.repr x) 2 = ⟪e3, x⟫ := by
      rw [B.repr_apply_apply, hB 2]; simp
    have hvx : ⟪v, x⟫ = Real.cos θ * ⟪u, x⟫ + Real.sin θ * ⟪e3, x⟫ := by
      conv_lhs => rw [hvdecomp]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hemiCone,
      h1x, h2x, hvx, B.repr.norm_map]
    tauto
  rw [hpre, hR.measure_preimage hW.measurableSet.nullMeasurableSet, volume_stdWedge θ h0 hpi]

theorem hemiCone_subset_ball (u : E3) : hemiCone u ⊆ {x : E3 | ‖x‖ < 1} := fun _ hx => hx.1

theorem volume_ne_top_of_subset_ball {S : Set E3} (hS : S ⊆ {x : E3 | ‖x‖ < 1}) :
    volume S ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [volume_unitBall]; exact ENNReal.ofReal_ne_top) (measure_mono hS)

theorem neg_hemiCone (u : E3) : -(hemiCone u) = hemiCone (-u) := by
  ext x; simp [hemiCone, inner_neg_left, inner_neg_right]

/-- Splitting a subset of the ball by the hyperplane orthogonal to `w`. -/
theorem volume_split_hemi (S : Set E3) (hS : MeasurableSet S) (hsub : S ⊆ {x : E3 | ‖x‖ < 1})
    {w : E3} (hw : w ≠ 0) :
    volume S = volume (S ∩ hemiCone w) + volume (S ∩ hemiCone (-w)) := by
  have e1 : S ∩ {x : E3 | 0 < ⟪w, x⟫} = S ∩ hemiCone w := by
    ext x; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hsub h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  have e2 : S ∩ {x : E3 | 0 < ⟪-w, x⟫} = S ∩ hemiCone (-w) := by
    ext x; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hsub h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  rw [← e1, ← e2]
  exact volume_split S hS hw

/-- Girard's theorem, in terms of the outer normals of the three sides. -/
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
theorem volume_cone_sphTriangle {a b c u v w : E3}
    (hbasis : ∀ x : E3, ∃ α β γ : ℝ, x = α • a + β • b + γ • c)
    (hua : 0 < ⟪u, a⟫) (hub : ⟪u, b⟫ = 0) (huc : ⟪u, c⟫ = 0)
    (hvb : 0 < ⟪v, b⟫) (hvc : ⟪v, c⟫ = 0) (hva : ⟪v, a⟫ = 0)
    (hwc : 0 < ⟪w, c⟫) (hwa : ⟪w, a⟫ = 0) (hwb : ⟪w, b⟫ = 0) :
    volume (Set.Ioo (0:ℝ) 1 • sphTriangle a b c) =
      volume (hemiCone u ∩ hemiCone v ∩ hemiCone w) := by
  have hu0 : u ≠ 0 := fun h => by rw [h] at hua; simp at hua
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvb; simp at hvb
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwc; simp at hwc
  have hinner : ∀ (p : E3) (α β γ : ℝ),
      ⟪p, α • a + β • b + γ • c⟫ = α * ⟪p, a⟫ + β * ⟪p, b⟫ + γ * ⟪p, c⟫ := by
    intro p α β γ
    simp [inner_add_right, real_inner_smul_right]
  -- the intersection of the three half-balls is contained in the cone over the triangle
  have hKsub : hemiCone u ∩ hemiCone v ∩ hemiCone w ⊆ Set.Ioo (0:ℝ) 1 • sphTriangle a b c := by
    rintro x ⟨⟨⟨hx1, hxu⟩, -, hxv⟩, -, hxw⟩
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxu
    have hnorm : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
    obtain ⟨α, β, γ, hx⟩ := hbasis x
    rw [hx, hinner u α β γ, hub, huc] at hxu
    rw [hx, hinner v α β γ, hva, hvc] at hxv
    rw [hx, hinner w α β γ, hwa, hwb] at hxw
    have hα : 0 ≤ α := by nlinarith
    have hβ : 0 ≤ β := by nlinarith
    have hγ : 0 ≤ γ := by nlinarith
    refine Set.mem_smul.mpr ⟨‖x‖, ⟨hnorm, hx1⟩, ‖x‖⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
    · refine ⟨‖x‖⁻¹ * α, ‖x‖⁻¹ * β, ‖x‖⁻¹ * γ, by positivity, by positivity, by positivity, ?_⟩
      rw [hx]
      simp [smul_add, smul_smul]
    · rw [smul_inv_smul₀ hnorm.ne']
  -- conversely the cone over the triangle is contained in it up to a null set
  have hZ : volume ({x : E3 | ⟪u, x⟫ = 0} ∪ {x : E3 | ⟪v, x⟫ = 0} ∪ {x : E3 | ⟪w, x⟫ = 0}) = 0 := by
    refine measure_union_null (measure_union_null (volume_inner_eq_zero hu0)
      (volume_inner_eq_zero hv0)) (volume_inner_eq_zero hw0)
  have hCsub : Set.Ioo (0:ℝ) 1 • sphTriangle a b c ⊆ (hemiCone u ∩ hemiCone v ∩ hemiCone w)
      ∪ ({x : E3 | ⟪u, x⟫ = 0} ∪ {x : E3 | ⟪v, x⟫ = 0} ∪ {x : E3 | ⟪w, x⟫ = 0}) := by
    intro x hx
    obtain ⟨t, ⟨ht0, ht1⟩, y, ⟨hy1, α, β, γ, hα, hβ, hγ, hy⟩, hxy⟩ := Set.mem_smul.mp hx
    have hnx : ‖x‖ < 1 := by
      rw [← hxy, norm_smul, hy1, Real.norm_eq_abs, abs_of_pos ht0, mul_one]
      exact ht1
    have hxe : x = (t * α) • a + (t * β) • b + (t * γ) • c := by
      rw [← hxy, hy]
      simp [smul_add, smul_smul]
    have hIu : ⟪u, x⟫ = (t * α) * ⟪u, a⟫ := by rw [hxe, hinner u, hub, huc]; ring
    have hIv : ⟪v, x⟫ = (t * β) * ⟪v, b⟫ := by rw [hxe, hinner v, hva, hvc]; ring
    have hIw : ⟪w, x⟫ = (t * γ) * ⟪w, c⟫ := by rw [hxe, hinner w, hwa, hwb]; ring
    rcases eq_or_lt_of_le hα with hα' | hα'
    · exact Or.inr (Or.inl (Or.inl (by simp [hIu, ← hα'])))
    rcases eq_or_lt_of_le hβ with hβ' | hβ'
    · exact Or.inr (Or.inl (Or.inr (by simp [hIv, ← hβ'])))
    rcases eq_or_lt_of_le hγ with hγ' | hγ'
    · exact Or.inr (Or.inr (by simp [hIw, ← hγ']))
    exact Or.inl ⟨⟨⟨hnx, by rw [hIu]; positivity⟩, hnx, by rw [hIv]; positivity⟩,
      hnx, by rw [hIw]; positivity⟩
  refine le_antisymm ?_ (measure_mono hKsub)
  calc volume (Set.Ioo (0:ℝ) 1 • sphTriangle a b c)
      ≤ volume ((hemiCone u ∩ hemiCone v ∩ hemiCone w)
        ∪ ({x : E3 | ⟪u, x⟫ = 0} ∪ {x : E3 | ⟪v, x⟫ = 0} ∪ {x : E3 | ⟪w, x⟫ = 0})) :=
        measure_mono hCsub
    _ = volume (hemiCone u ∩ hemiCone v ∩ hemiCone w) := measure_union_null_right hZ

/-! ### The Gauss-Bonnet formula for a spherical triangle (Girard's theorem) -/

/-- **Gauss-Bonnet for a spherical triangle** (Girard's theorem): the sum of the interior angles
of a geodesic triangle on the unit sphere exceeds `π` by the area of the triangle. -/
theorem gauss_bonnet_polygon (a b c : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hind : LinearIndependent ℝ ![a, b, c]) :
    sphAngle a b c + sphAngle b c a + sphAngle c a b = π + sphArea (sphTriangle a b c) := by
  have hd : ⟪a, cross b c⟫ ≠ 0 := inner_cross_ne_zero_of_linearIndependent hind
  set d := ⟪a, cross b c⟫ with hdd
  have r1 : ⟪b, cross c a⟫ = d := (inner_cross_rotate a b c).symm
  have r2 : ⟪c, cross a b⟫ = d := (inner_cross_rotate b c a).symm.trans r1
  -- the three outer normals, scaled by `d` so that they point to the correct side
  set U := d • cross b c with hU
  set V := d • cross c a with hV
  set W := d • cross a b with hW
  have iUa : ⟪U, a⟫ = d * d := by
    rw [hU, real_inner_smul_left, real_inner_comm]
  have iUb : ⟪U, b⟫ = 0 := by rw [hU, real_inner_smul_left, inner_cross_left, mul_zero]
  have iUc : ⟪U, c⟫ = 0 := by rw [hU, real_inner_smul_left, inner_cross_right, mul_zero]
  have iVb : ⟪V, b⟫ = d * d := by rw [hV, real_inner_smul_left, real_inner_comm, r1]
  have iVc : ⟪V, c⟫ = 0 := by rw [hV, real_inner_smul_left, inner_cross_left, mul_zero]
  have iVa : ⟪V, a⟫ = 0 := by rw [hV, real_inner_smul_left, inner_cross_right, mul_zero]
  have iWc : ⟪W, c⟫ = d * d := by rw [hW, real_inner_smul_left, real_inner_comm, r2]
  have iWa : ⟪W, a⟫ = 0 := by rw [hW, real_inner_smul_left, inner_cross_left, mul_zero]
  have iWb : ⟪W, b⟫ = 0 := by rw [hW, real_inner_smul_left, inner_cross_right, mul_zero]
  have hdd2 : 0 < d * d := mul_self_pos.mpr hd
  have hU0 : U ≠ 0 := fun h => by rw [h] at iUa; simp at iUa; exact hd (by nlinarith)
  have hV0 : V ≠ 0 := fun h => by rw [h] at iVb; simp at iVb; exact hd (by nlinarith)
  have hW0 : W ≠ 0 := fun h => by rw [h] at iWc; simp at iWc; exact hd (by nlinarith)
  -- normalise them
  set u := ‖U‖⁻¹ • U with hu'
  set v := ‖V‖⁻¹ • V with hv'
  set w := ‖W‖⁻¹ • W with hw'
  have nU : (0:ℝ) < ‖U‖⁻¹ := by positivity
  have nV : (0:ℝ) < ‖V‖⁻¹ := by positivity
  have nW : (0:ℝ) < ‖W‖⁻¹ := by positivity
  have hu : ‖u‖ = 1 := by rw [hu']; exact norm_smul_inv_norm (𝕜 := ℝ) hU0
  have hv : ‖v‖ = 1 := by rw [hv']; exact norm_smul_inv_norm (𝕜 := ℝ) hV0
  have hw : ‖w‖ = 1 := by rw [hw']; exact norm_smul_inv_norm (𝕜 := ℝ) hW0
  have jUa : 0 < ⟪u, a⟫ := by rw [hu', real_inner_smul_left, iUa]; positivity
  have jUb : ⟪u, b⟫ = 0 := by rw [hu', real_inner_smul_left, iUb, mul_zero]
  have jUc : ⟪u, c⟫ = 0 := by rw [hu', real_inner_smul_left, iUc, mul_zero]
  have jVb : 0 < ⟪v, b⟫ := by rw [hv', real_inner_smul_left, iVb]; positivity
  have jVc : ⟪v, c⟫ = 0 := by rw [hv', real_inner_smul_left, iVc, mul_zero]
  have jVa : ⟪v, a⟫ = 0 := by rw [hv', real_inner_smul_left, iVa, mul_zero]
  have jWc : 0 < ⟪w, c⟫ := by rw [hw', real_inner_smul_left, iWc]; positivity
  have jWa : ⟪w, a⟫ = 0 := by rw [hw', real_inner_smul_left, iWa, mul_zero]
  have jWb : ⟪w, b⟫ = 0 := by rw [hw', real_inner_smul_left, iWb, mul_zero]
  -- the normals are pairwise non-collinear
  have nuv : u ≠ v := fun h => by rw [h, jVa] at jUa; exact lt_irrefl 0 jUa
  have nuv' : u ≠ -v := fun h => by
    rw [h, inner_neg_left, jVa, neg_zero] at jUa; exact lt_irrefl 0 jUa
  have nvw : v ≠ w := fun h => by rw [h, jWb] at jVb; exact lt_irrefl 0 jVb
  have nvw' : v ≠ -w := fun h => by
    rw [h, inner_neg_left, jWb, neg_zero] at jVb; exact lt_irrefl 0 jVb
  have nuw : u ≠ w := fun h => by rw [h, jWa] at jUa; exact lt_irrefl 0 jUa
  have nuw' : u ≠ -w := fun h => by
    rw [h, inner_neg_left, jWa, neg_zero] at jUa; exact lt_irrefl 0 jUa
  -- `a`, `b`, `c` span the space
  have hcard : Fintype.card (Fin 3) = finrank ℝ E3 := by simp
  have hbasis : ∀ x : E3, ∃ α β γ : ℝ, x = α • a + β • b + γ • c := by
    intro x
    have hB : ⇑(basisOfLinearIndependentOfCardEqFinrank hind hcard) = ![a, b, c] :=
      coe_basisOfLinearIndependentOfCardEqFinrank hind hcard
    have hsum := (basisOfLinearIndependentOfCardEqFinrank hind hcard).sum_repr x
    refine ⟨(basisOfLinearIndependentOfCardEqFinrank hind hcard).repr x 0,
      (basisOfLinearIndependentOfCardEqFinrank hind hcard).repr x 1,
      (basisOfLinearIndependentOfCardEqFinrank hind hcard).repr x 2, ?_⟩
    conv_lhs => rw [← hsum]
    rw [Fin.sum_univ_three, hB]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
  -- the area of the triangle
  have harea : sphArea (sphTriangle a b c)
      = 2 * π - InnerProductGeometry.angle u v - InnerProductGeometry.angle v w
        - InnerProductGeometry.angle w u := by
    rw [sphArea, volume_cone_sphTriangle hbasis jUa jUb jUc jVb jVc jVa jWc jWa jWb,
      volume_triangleCone hu hv hw nuv nuv' nvw nvw' nuw nuw']
    ring
  -- the angles of the triangle in terms of the normals
  have auv : InnerProductGeometry.angle u v = InnerProductGeometry.angle (cross b c) (cross c a) := by
    rw [hu', hv', InnerProductGeometry.angle_smul_left_of_pos _ _ nU,
      InnerProductGeometry.angle_smul_right_of_pos _ _ nV, hU, hV,
      InnerProductGeometry.angle_smul_smul hd]
  have avw : InnerProductGeometry.angle v w = InnerProductGeometry.angle (cross c a) (cross a b) := by
    rw [hv', hw', InnerProductGeometry.angle_smul_left_of_pos _ _ nV,
      InnerProductGeometry.angle_smul_right_of_pos _ _ nW, hV, hW,
      InnerProductGeometry.angle_smul_smul hd]
  have awu : InnerProductGeometry.angle w u = InnerProductGeometry.angle (cross a b) (cross b c) := by
    rw [hw', hu', InnerProductGeometry.angle_smul_left_of_pos _ _ nW,
      InnerProductGeometry.angle_smul_right_of_pos _ _ nU, hW, hU,
      InnerProductGeometry.angle_smul_smul hd]
  rw [harea, sphAngle_eq_pi_sub a b c ha, sphAngle_eq_pi_sub b c a hb,
    sphAngle_eq_pi_sub c a b hc, auv, avw, awu]
  ring

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

