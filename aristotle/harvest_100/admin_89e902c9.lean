import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/
def unitBall3 : Set E3 := {x : E3 | ‖x‖ ≤ 1}

section

variable (nA nB nC : E3)

/-- The part of the unit ball on the side `s` of the plane normal to `nA`. -/
def Oct1 (s : ℝ) : Set E3 := unitBall3 ∩ {x | 0 ≤ s * ⟪x, nA⟫}

/-- The part of the unit ball on prescribed sides of the planes normal to `nA`, `nB`. -/
def Oct2 (s t : ℝ) : Set E3 := Oct1 nA s ∩ {x | 0 ≤ t * ⟪x, nB⟫}

/-- The part of the unit ball on prescribed sides of the three planes. -/
def Oct3 (s t u : ℝ) : Set E3 := Oct2 nA nB s t ∩ {x | 0 ≤ u * ⟪x, nC⟫}

lemma measurableSet_halfspace (s : ℝ) (n : E3) : MeasurableSet {x : E3 | 0 ≤ s * ⟪x, n⟫} := by
  have : Continuous fun x : E3 => s * ⟪x, n⟫ := by
    exact continuous_const.mul (continuous_id.inner continuous_const)
  exact measurableSet_le measurable_const this.measurable

lemma unitBall3_eq : unitBall3 = closedBall (0 : E3) 1 := by ext x; simp [unitBall3]

lemma measurableSet_unitBall3 : MeasurableSet unitBall3 := by
  rw [unitBall3_eq]; exact measurableSet_closedBall

lemma measurableSet_Oct1 (s : ℝ) : MeasurableSet (Oct1 nA s) :=
  measurableSet_unitBall3.inter (measurableSet_halfspace s nA)

lemma measurableSet_Oct2 (s t : ℝ) : MeasurableSet (Oct2 nA nB s t) :=
  (measurableSet_Oct1 nA s).inter (measurableSet_halfspace t nB)

lemma measurableSet_Oct3 (s t u : ℝ) : MeasurableSet (Oct3 nA nB nC s t u) :=
  (measurableSet_Oct2 nA nB s t).inter (measurableSet_halfspace u nC)

lemma Oct1_subset (s : ℝ) : Oct1 nA s ⊆ unitBall3 := inter_subset_left

lemma Oct2_subset (s t : ℝ) : Oct2 nA nB s t ⊆ unitBall3 :=
  inter_subset_left.trans (Oct1_subset nA s)

lemma Oct3_subset (s t u : ℝ) : Oct3 nA nB nC s t u ⊆ unitBall3 :=
  inter_subset_left.trans (Oct2_subset nA nB s t)

lemma volume_unitBall3 : volume unitBall3 = ENNReal.ofReal (4 * π / 3) := by
  rw [unitBall3_eq]; exact volume_closedBall_E3

lemma volume_unitBall3_ne_top : volume unitBall3 ≠ ⊤ := by
  rw [volume_unitBall3]; exact ENNReal.ofReal_ne_top

lemma volume_ne_top_of_subset {S : Set E3} (h : S ⊆ unitBall3) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top volume_unitBall3_ne_top (measure_mono h)

/-- The antipodal map exchanges opposite octants. -/
lemma volume_Oct3_neg (s t u : ℝ) :
    volume (Oct3 nA nB nC (-s) (-t) (-u)) = volume (Oct3 nA nB nC s t u) := by
  rw [← volume_neg (Oct3 nA nB nC s t u)]
  congr 1
  ext x
  simp only [Oct3, Oct2, Oct1, unitBall3, mem_preimage, mem_inter_iff, mem_setOf_eq,
    inner_neg_left, norm_neg]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩ <;> nlinarith [h2, h3, h4]
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩ <;> nlinarith [h2, h3, h4]

variable {nA nB nC}

/-- Splitting a subset of the ball by the plane normal to `n`, in signed form. -/
lemma volume_split' (S : Set E3) (hS : MeasurableSet S) (n : E3) (hn : n ≠ 0) :
    volume S = volume (S ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, n⟫}) + volume (S ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, n⟫}) := by
  rw [volume_split S hS n hn]
  congr 2 <;> · ext x; simp only [mem_inter_iff, mem_setOf_eq, one_mul, neg_mul, neg_nonneg]

lemma volume_split_ball (hnA : nA ≠ 0) :
    volume unitBall3 = volume (Oct1 nA 1) + volume (Oct1 nA (-1)) :=
  volume_split' unitBall3 measurableSet_unitBall3 nA hnA

lemma volume_split_Oct1 (hnB : nB ≠ 0) (s : ℝ) :
    volume (Oct1 nA s) = volume (Oct2 nA nB s 1) + volume (Oct2 nA nB s (-1)) :=
  volume_split' _ (measurableSet_Oct1 nA s) nB hnB

lemma volume_split_Oct2 (hnC : nC ≠ 0) (s t : ℝ) :
    volume (Oct2 nA nB s t) = volume (Oct3 nA nB nC s t 1) + volume (Oct3 nA nB nC s t (-1)) :=
  volume_split' _ (measurableSet_Oct2 nA nB s t) nC hnC

/-- A wedge, described as an intersection. -/
lemma wedge_eq_inter (m n : E3) :
    {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = unitBall3 ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, m⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, n⟫} := by
  ext x
  simp only [unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
  tauto

lemma measurableSet_wedge (m n : E3) :
    MeasurableSet {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫} := by
  rw [wedge_eq_inter]
  exact (measurableSet_unitBall3.inter (measurableSet_halfspace 1 m)).inter
    (measurableSet_halfspace 1 n)

/-- The wedge at the vertex `A` splits into two octants. -/
lemma volume_wedgeA_split (hnA : nA ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫}
      = volume (Oct3 nA nB nC 1 1 1) + volume (Oct3 nA nB nC (-1) 1 1) := by
  have e1 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, nA⟫}
      = Oct3 nA nB nC 1 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  have e2 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫} ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, nA⟫}
      = Oct3 nA nB nC (-1) 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  rw [volume_split' _ (measurableSet_wedge nB nC) nA hnA, e1, e2]

/-- The wedge at the vertex `B` splits into two octants. -/
lemma volume_wedgeB_split (hnB : nB ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nC⟫}
      = volume (Oct3 nA nB nC 1 1 1) + volume (Oct3 nA nB nC 1 (-1) 1) := by
  have e1 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nC⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, nB⟫}
      = Oct3 nA nB nC 1 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  have e2 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nC⟫} ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, nB⟫}
      = Oct3 nA nB nC 1 (-1) 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  rw [volume_split' _ (measurableSet_wedge nA nC) nB hnB, e1, e2]

/-- The wedge at the vertex `C` splits into two octants. -/
lemma volume_wedgeC_split (hnC : nC ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫}
      = volume (Oct3 nA nB nC 1 1 1) + volume (Oct3 nA nB nC 1 1 (-1)) := by
  have e1 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, nC⟫}
      = Oct3 nA nB nC 1 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  have e2 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫} ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, nC⟫}
      = Oct3 nA nB nC 1 1 (-1) := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  rw [volume_split' _ (measurableSet_wedge nA nB) nC hnC, e1, e2]

end

end Math

import RequestProject.Defs

/-!
# The volume of a wedge of the unit ball

The main result of this file is `Math.volume_wedge`: the part of the closed unit ball of
`E3` cut out by two half-spaces through the origin with unit normals `m`, `n` has volume
`2 * (π - angle m n) / 3`; equivalently, the corresponding "lune" of the unit sphere,
whose dihedral angle is `π - angle m n`, has area twice its angle.
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- `∫_0^1 2 r √(1-r²) dr = 2/3`. -/
lemma integral_radial : ∫ r in (0:ℝ)..1, 2 * r * √(1 - r ^ 2) = 2 / 3 := by
  have hcont : ContinuousOn (fun r : ℝ => -2 / 3 * ((1 - r ^ 2) * √(1 - r ^ 2))) (Icc 0 1) := by
    fun_prop
  have hderiv : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => -2 / 3 * ((1 - r ^ 2) * √(1 - r ^ 2))) (2 * r * √(1 - r ^ 2)) r := by
    intro r hr
    have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have h1 : (1 : ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
    have hsq : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hpos.le
    have hne : √(1 - r ^ 2) ≠ 0 := by positivity
    have hg : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
      simpa using ((hasDerivAt_pow 2 r).const_sub 1)
    have hs : HasDerivAt (fun r : ℝ => √(1 - r ^ 2)) (1 / (2 * √(1 - r ^ 2)) * -(2 * r)) r :=
      (Real.hasDerivAt_sqrt h1).comp r hg
    have hmul : HasDerivAt (fun r : ℝ => (1 - r ^ 2) * √(1 - r ^ 2))
        (-(2 * r) * √(1 - r ^ 2) + (1 - r ^ 2) * (1 / (2 * √(1 - r ^ 2)) * -(2 * r))) r :=
      hg.mul hs
    have key : ∀ s : ℝ, s ≠ 0 → s ^ 2 = 1 - r ^ 2 →
        -2 / 3 * (-(2 * r) * s + (1 - r ^ 2) * (1 / (2 * s) * -(2 * r))) = 2 * r * s := by
      intro s hs0 hs2
      rw [← hs2]
      field_simp
      ring
    exact (hmul.const_mul (-2 / 3 : ℝ)).congr_deriv (key _ hne hsq)
  have hint : IntervalIntegrable (fun r : ℝ => 2 * r * √(1 - r ^ 2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num) hcont
    (fun r hr => (hderiv r hr).hasDerivWithinAt) hint]
  norm_num

lemma lintegral_radial :
    ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (2 * r * √(1 - r ^ 2)) = ENNReal.ofReal (2 / 3) := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext r
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h
      rcases le_total r 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · rcases eq_or_lt_of_le h' with h'' | h''
        · exact Or.inl ⟨h, h''.ge⟩
        · exact Or.inr h''
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  have hmeasf : Measurable fun r : ℝ => ENNReal.ofReal (2 * r * √(1 - r ^ 2)) := by fun_prop
  have hzero : ∫⁻ r in Ioi (1:ℝ), ENNReal.ofReal (2 * r * √(1 - r ^ 2)) = 0 := by
    rw [setLIntegral_eq_zero_iff' measurableSet_Ioi hmeasf.aemeasurable]
    filter_upwards with r hr
    have : √(1 - r ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith [mem_Ioi.mp hr])
    simp [this]
  rw [hsplit, lintegral_union measurableSet_Ioi (by simp [Set.disjoint_left]), hzero, add_zero]
  have hint : IntegrableOn (fun r : ℝ => 2 * r * √(1 - r ^ 2)) (Ioc 0 1) volume := by
    apply Continuous.integrableOn_Ioc
    fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal hint ?_]
  · congr 1
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact integral_radial
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have h0 : (0:ℝ) ≤ r := hr.1.le
    positivity

/-- The length of a vertical slice of the unit ball. -/
lemma volume_sq_le (c : ℝ) : volume {t : ℝ | t ^ 2 ≤ c} = ENNReal.ofReal (2 * √c) := by
  rcases lt_or_ge c 0 with hc | hc
  · have hempty : {t : ℝ | t ^ 2 ≤ c} = ∅ := by
      ext t
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      nlinarith [sq_nonneg t]
    rw [hempty, Real.sqrt_eq_zero_of_nonpos hc.le]
    simp
  · have hset : {t : ℝ | t ^ 2 ≤ c} = Icc (-√c) (√c) := by
      ext t
      simp only [mem_setOf_eq, mem_Icc]
      constructor
      · intro h
        constructor <;> nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c, sq_nonneg (t - √c),
          sq_nonneg (t + √c)]
      · rintro ⟨h1, h2⟩
        nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c]
    rw [hset, Real.volume_Icc]
    congr 1
    ring

/-- Identification of `ℝ² × ℝ` with `Fin 3 → ℝ`. -/
noncomputable def coords3 : (ℝ × ℝ) × ℝ → (Fin 3 → ℝ) := fun q => ![q.1.1, q.1.2, q.2]

lemma measurePreserving_coords3 : MeasurePreserving coords3 volume volume := by
  have h1 : MeasurePreserving (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ)) volume volume :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have h2 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow.symm : (ℝ × ℝ) → (Fin 2 → ℝ)))
      volume volume :=
    MeasurePreserving.prod (MeasurePreserving.id _) (volume_preserving_finTwoArrow ℝ).symm
  have h3 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  have hcomp := (h3.comp h2).comp h1
  convert hcomp using 1
  funext q
  obtain ⟨⟨x, y⟩, t⟩ := q
  funext i
  fin_cases i <;>
    simp [coords3, MeasurableEquiv.piFinSuccAbove, Fin.insertNth, Fin.succAboveCases,
      MeasurableEquiv.finTwoArrow]

/-- Fubini in the last coordinate: the volume of a region of the unit ball lying over a
planar region `D`. -/
lemma volume_pi3 (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    volume {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D}
      = ∫⁻ p in D, ENNReal.ofReal (2 * √(1 - p.1 ^ 2 - p.2 ^ 2)) := by
  have hSmeas :
      MeasurableSet {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D} := by
    refine MeasurableSet.inter ?_ ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1) hD)
    have h : Measurable fun z : Fin 3 → ℝ => z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by fun_prop
    exact measurableSet_le h measurable_const
  rw [← measurePreserving_coords3.measure_preimage hSmeas.nullMeasurableSet]
  have hpre : coords3 ⁻¹' {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D}
      = {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D} := by
    ext q
    simp [coords3]
  rw [hpre]
  have hS'meas :
      MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D} := by
    refine MeasurableSet.inter ?_ (measurable_fst hD)
    have h : Measurable fun q : (ℝ × ℝ) × ℝ => q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 := by fun_prop
    exact measurableSet_le h measurable_const
  rw [show (volume : Measure ((ℝ × ℝ) × ℝ)) = (volume : Measure (ℝ × ℝ)).prod volume from rfl,
    Measure.prod_apply hS'meas, ← lintegral_indicator hD]
  congr 1
  funext p
  by_cases hp : p ∈ D
  · rw [Set.indicator_of_mem hp]
    have hslice : (Prod.mk p ⁻¹' {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D})
        = {t : ℝ | t ^ 2 ≤ 1 - p.1 ^ 2 - p.2 ^ 2} := by
      ext t
      simp only [mem_preimage, mem_setOf_eq, hp, and_true]
      constructor <;> intro h <;> linarith
    rw [hslice, volume_sq_le]
  · rw [Set.indicator_of_notMem hp]
    have hslice : (Prod.mk p ⁻¹' {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D})
        = ∅ := by
      ext t
      simp [hp]
    rw [hslice]
    simp

/-- The angular condition describing the sector. -/
lemma sector_theta (psi theta : ℝ) (h0 : 0 < psi) (hpi : psi < π) (hθ : theta ∈ Ioo (-π) π) :
    (0 ≤ cos theta ∧ 0 ≤ cos psi * cos theta + sin psi * sin theta)
      ↔ theta ∈ Icc (psi - π / 2) (π / 2) := by
  have hcs : cos psi * cos theta + sin psi * sin theta = cos (theta - psi) := by
    rw [Real.cos_sub]; ring
  rw [hcs]
  obtain ⟨hθ1, hθ2⟩ := hθ
  constructor
  · rintro ⟨hc1, hc2⟩
    have hup : theta ≤ π / 2 := by
      by_contra hcon
      push_neg at hcon
      exact absurd hc1 (not_le.mpr
        (Real.cos_neg_of_pi_div_two_lt_of_lt hcon (by linarith [Real.pi_pos])))
    have hlow : -(π / 2) ≤ theta := by
      by_contra hcon
      push_neg at hcon
      have : cos theta < 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
      linarith
    refine ⟨?_, hup⟩
    by_contra hcon
    push_neg at hcon
    have : cos (theta - psi) < 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    linarith
  · rintro ⟨hl, hu⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, hu⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩

/-- An integral over a product set of a function of the first variable. -/
lemma lintegral_prod_fst (f : ℝ → ℝ≥0∞) (hf : Measurable f) (s t : Set ℝ) :
    ∫⁻ p in s ×ˢ t, f p.1 = (∫⁻ r in s, f r) * volume t := by
  rw [(by rfl : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume),
    ← Measure.prod_restrict]
  rw [show (fun p : ℝ × ℝ => f p.1) = (fun p : ℝ × ℝ => f p.1 * (fun _ : ℝ => (1:ℝ≥0∞)) p.2) by
    funext p; simp]
  rw [lintegral_prod_mul hf.aemeasurable aemeasurable_const]
  simp

/-- The planar integral over the sector cut out by two half-planes. -/
lemma lintegral_sector (ψ : ℝ) (h0 : 0 < ψ) (hπ : ψ < π) :
    ∫⁻ p in {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ cos ψ * p.1 + sin ψ * p.2},
        ENNReal.ofReal (2 * √(1 - p.1 ^ 2 - p.2 ^ 2))
      = ENNReal.ofReal (2 * (π - ψ) / 3) := by
  set D : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ cos ψ * p.1 + sin ψ * p.2} with hDdef
  set T : Set ℝ := Icc (ψ - π / 2) (π / 2) with hTdef
  have hDmeas : MeasurableSet D := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const measurable_fst
    · exact measurableSet_le measurable_const
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
  rw [← lintegral_indicator hDmeas, ← lintegral_comp_polarCoord_symm]
  have hstep : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        D.indicator (fun p : ℝ × ℝ => ENNReal.ofReal (2 * √(1 - p.1 ^ 2 - p.2 ^ 2)))
          (polarCoord.symm p)
      = ∫⁻ p in polarCoord.target,
          (Ioi (0:ℝ) ×ˢ T).indicator (fun p : ℝ × ℝ =>
            ENNReal.ofReal (2 * p.1 * √(1 - p.1 ^ 2))) p := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet ?_
    rintro ⟨r, theta⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨hr, hθ⟩ := hp
    simp only [mem_Ioi] at hr
    simp only [polarCoord_symm_apply, smul_eq_mul]
    have hcos : (r * cos theta) ^ 2 + (r * sin theta) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    have hmem : ((r * cos theta, r * sin theta) ∈ D) ↔ (r, theta) ∈ Ioi (0:ℝ) ×ˢ T := by
      simp only [hDdef, mem_setOf_eq, Set.mem_prod, mem_Ioi, hr, true_and]
      rw [← sector_theta ψ theta h0 hπ hθ]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : 0 ≤ cos theta * r := by rw [mul_comm]; exact h1
        refine ⟨nonneg_of_mul_nonneg_left h1' hr, ?_⟩
        have h2' : 0 ≤ (cos ψ * cos theta + sin ψ * sin theta) * r := by nlinarith [h2]
        exact nonneg_of_mul_nonneg_left h2' hr
      · rintro ⟨h1, h2⟩
        exact ⟨by positivity, by nlinarith [h2]⟩
    by_cases hin : (r, theta) ∈ Ioi (0:ℝ) ×ˢ T
    · rw [Set.indicator_of_mem hin, Set.indicator_of_mem (hmem.mpr hin)]
      rw [show (1 : ℝ) - (r * cos theta) ^ 2 - (r * sin theta) ^ 2 = 1 - r ^ 2 by nlinarith [hcos]]
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      ring
    · rw [Set.indicator_of_notMem hin, Set.indicator_of_notMem (fun h => hin (hmem.mp h))]
      simp
  rw [hstep]
  have hsub : Ioi (0:ℝ) ×ˢ T ⊆ polarCoord.target := by
    rw [polarCoord_target]
    rintro ⟨r, theta⟩ ⟨hr, hθ⟩
    refine ⟨hr, ?_⟩
    simp only [hTdef, mem_Icc] at hθ
    exact ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
  have hTmeas : MeasurableSet (Ioi (0:ℝ) ×ˢ T) := measurableSet_Ioi.prod measurableSet_Icc
  rw [lintegral_indicator hTmeas, Measure.restrict_restrict hTmeas, inter_eq_left.mpr hsub,
    lintegral_prod_fst (fun r => ENNReal.ofReal (2 * r * √(1 - r ^ 2))) (by fun_prop)
      (Ioi (0:ℝ)) T, lintegral_radial, hTdef, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- The volume of the standard wedge of the unit ball with dihedral angle `π - ψ`. -/
lemma volume_standard_wedge (ψ : ℝ) (h0 : 0 < ψ) (hπ : ψ < π) :
    volume {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1}
      = ENNReal.ofReal (2 * (π - ψ) / 3) := by
  set D : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ cos ψ * p.1 + sin ψ * p.2} with hDdef
  have hDmeas : MeasurableSet D :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
  have hnm : Measurable fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ := by fun_prop
  have hc0 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 0 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 0).measurable
  have hc1 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 1 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 1).measurable
  have hSmeas : MeasurableSet
      {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1} :=
    (measurableSet_le hnm measurable_const).inter
      ((measurableSet_le measurable_const hc0).inter
        (measurableSet_le measurable_const
          ((measurable_const.mul hc0).add (measurable_const.mul hc1))))
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hSmeas.nullMeasurableSet]
  have hpre : (WithLp.toLp 2) ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1}
      = {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D} := by
    ext z
    simp only [mem_preimage, mem_setOf_eq, hDdef]
    have hnorm : ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 3))‖ = √(z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      rw [Fin.sum_univ_three]
      simp [sq_abs]
    rw [hnorm, Real.sqrt_le_one]
  rw [hpre, volume_pi3 D hDmeas, hDdef, lintegral_sector ψ h0 hπ]

/-- Measurability of the standard wedge. -/
lemma measurableSet_standard_wedge (ψ : ℝ) : MeasurableSet
    {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1} := by
  have hnm : Measurable fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ := by fun_prop
  have hc0 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 0 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 0).measurable
  have hc1 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 1 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 1).measurable
  exact (measurableSet_le hnm measurable_const).inter
      ((measurableSet_le measurable_const hc0).inter
        (measurableSet_le measurable_const
          ((measurable_const.mul hc0).add (measurable_const.mul hc1))))

/-- Any pair of orthonormal vectors of `E3` extends to an orthonormal basis. -/
lemma exists_orthonormalBasis_pair (e0 e1 : E3) (h0 : ‖e0‖ = 1) (h1 : ‖e1‖ = 1)
    (h01 : ⟪e1, e0⟫ = 0) : ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e0 ∧ b 1 = e1 := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp [E3]
  have horth : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![e0, e1, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    have h10 : ⟪e0, e1⟫ = 0 := by rw [real_inner_comm]; exact h01
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.restrict, h0, h1, h01, h10]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp)⟩

/-- The volume of the wedge of the unit ball cut out by two half-spaces with unit normals
`m` and `n`. -/
lemma volume_wedge_unit (m n : E3) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1)
    (h0 : 0 < InnerProductGeometry.angle m n) (hπ : InnerProductGeometry.angle m n < π) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = ENNReal.ofReal (2 * (π - InnerProductGeometry.angle m n) / 3) := by
  set ψ := InnerProductGeometry.angle m n with hψ
  have hsin : 0 < sin ψ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hcosmn : ⟪m, n⟫ = cos ψ := by
    rw [hψ, InnerProductGeometry.cos_angle, hm, hn]; ring
  have hcosnm : ⟪n, m⟫ = cos ψ := by rw [real_inner_comm]; exact hcosmn
  set e1 : E3 := (sin ψ)⁻¹ • (n - cos ψ • m) with he1def
  have hnsub : ‖n - cos ψ • m‖ = sin ψ := by
    have h2 : ‖n - cos ψ • m‖ ^ 2 = (sin ψ) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, hn, hm, real_inner_smul_right, hcosnm, Real.norm_eq_abs]
      have := Real.sin_sq_add_cos_sq ψ
      simp only [mul_one]
      nlinarith [sq_abs (cos ψ)]
    nlinarith [norm_nonneg (n - cos ψ • m), hsin]
  have he1norm : ‖e1‖ = 1 := by
    rw [he1def, norm_smul, hnsub]
    simp [abs_of_pos hsin, inv_mul_cancel₀ (ne_of_gt hsin)]
  have he1m : ⟪e1, m⟫ = 0 := by
    rw [he1def, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hm, hcosnm]
    ring
  have hn_eq : n = cos ψ • m + sin ψ • e1 := by
    rw [he1def, smul_inv_smul₀ (ne_of_gt hsin)]
    abel
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_pair m e1 hm he1norm he1m
  have hpre : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = b.repr ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1} := by
    ext x
    have e0' : (b.repr x) 0 = ⟪x, m⟫ := by
      rw [show ((b.repr x) 0 : ℝ) = (b.repr x).ofLp 0 from rfl, b.repr_apply_apply, hb0,
        real_inner_comm]
    have e1' : (b.repr x) 1 = ⟪x, e1⟫ := by
      rw [show ((b.repr x) 1 : ℝ) = (b.repr x).ofLp 1 from rfl, b.repr_apply_apply, hb1,
        real_inner_comm]
    have hnorm : ‖b.repr x‖ = ‖x‖ := b.repr.norm_map x
    have hinn : ⟪x, n⟫ = cos ψ * ⟪x, m⟫ + sin ψ * ⟪x, e1⟫ := by
      rw [hn_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp only [mem_preimage, mem_setOf_eq, e0', e1', hnorm, hinn]
  rw [hpre, (b.measurePreserving_repr).measure_preimage
      (measurableSet_standard_wedge ψ).nullMeasurableSet, volume_standard_wedge ψ h0 hπ]

/-- The volume of the wedge of the unit ball cut out by two half-spaces with (nonzero)
normals `m` and `n`. -/
lemma volume_wedge (m n : E3) (hm : m ≠ 0) (hn : n ≠ 0)
    (h0 : 0 < InnerProductGeometry.angle m n) (hπ : InnerProductGeometry.angle m n < π) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = ENNReal.ofReal (2 * (π - InnerProductGeometry.angle m n) / 3) := by
  have hmn : (0:ℝ) < ‖m‖ := norm_pos_iff.mpr hm
  have hnn : (0:ℝ) < ‖n‖ := norm_pos_iff.mpr hn
  set m' : E3 := ‖m‖⁻¹ • m with hm'def
  set n' : E3 := ‖n‖⁻¹ • n with hn'def
  have hm'norm : ‖m'‖ = 1 := by
    rw [hm'def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hmn)]
  have hn'norm : ‖n'‖ = 1 := by
    rw [hn'def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hnn)]
  have hang : InnerProductGeometry.angle m' n' = InnerProductGeometry.angle m n := by
    rw [hm'def, hn'def, InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr hmn),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr hnn)]
  have hset : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m'⟫ ∧ 0 ≤ ⟪x, n'⟫} := by
    ext x
    simp only [mem_setOf_eq, hm'def, hn'def, real_inner_smul_right]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by positivity, by positivity⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · exact nonneg_of_mul_nonneg_left (by rw [mul_comm]; exact h2) (inv_pos.mpr hmn)
      · exact nonneg_of_mul_nonneg_left (by rw [mul_comm]; exact h3) (inv_pos.mpr hnn)
  rw [hset, volume_wedge_unit m' n' hm'norm hn'norm (hang ▸ h0) (hang ▸ hπ), hang]

/-- The volume of the closed unit ball of `E3`. -/
lemma volume_closedBall_E3 : volume (closedBall (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin]
  rw [show ((3:ℕ):ℝ) / 2 + 1 = 1 / 2 + 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hpi : (0:ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h3 : √π ^ 3 = π * √π := by
    rw [pow_succ, pow_two, Real.mul_self_sqrt Real.pi_pos.le]
  field_simp [h3]
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- A hyperplane through the origin is null. -/
lemma volume_hyperplane (n : E3) (hn : n ≠ 0) : volume {x : E3 | ⟪x, n⟫ = 0} = 0 := by
  have hset : {x : E3 | ⟪x, n⟫ = 0}
      = ((LinearMap.ker (innerSL ℝ n).toLinearMap : Submodule ℝ E3) : Set E3) := by
    ext x
    simp [LinearMap.mem_ker, real_inner_comm x n]
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [h]; trivial
  simp only [LinearMap.mem_ker] at hmem
  exact hn (by simpa using hmem)

/-- Splitting a set along a hyperplane through the origin. -/
lemma volume_split (S : Set E3) (hS : MeasurableSet S) (n : E3) (hn : n ≠ 0) :
    volume S = volume (S ∩ {x | 0 ≤ ⟪x, n⟫}) + volume (S ∩ {x | ⟪x, n⟫ ≤ 0}) := by
  have hmeas : Measurable fun x : E3 => ⟪x, n⟫ :=
    (continuous_id.inner continuous_const).measurable
  have hnull : volume ((S ∩ {x : E3 | 0 ≤ ⟪x, n⟫}) ∩ (S ∩ {x : E3 | ⟪x, n⟫ ≤ 0})) = 0 := by
    refine measure_mono_null ?_ (volume_hyperplane n hn)
    rintro x ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    exact le_antisymm h2 h1
  have hunion : (S ∩ {x : E3 | 0 ≤ ⟪x, n⟫}) ∪ (S ∩ {x : E3 | ⟪x, n⟫ ≤ 0}) = S := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_total (0:ℝ) ⟪x, n⟫ with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hkey := measure_union_add_inter (μ := (volume : Measure E3)) (s := S ∩ {x | 0 ≤ ⟪x, n⟫})
    (t := S ∩ {x | ⟪x, n⟫ ≤ 0}) (hS.inter (measurableSet_le hmeas measurable_const))
  rw [hunion, hnull, add_zero] at hkey
  exact hkey

/-- Volume is invariant under the antipodal map. -/
lemma volume_neg (S : Set E3) : volume ((fun x : E3 => -x) ⁻¹' S) = volume S := by
  rw [show (fun x : E3 => -x) ⁻¹' S = -S from rfl]
  exact Measure.measure_neg volume S

end Math

import Mathlib

/-!
# Basic definitions for the spherical Gauss–Bonnet (Girard) theorem

We work in `E3 = EuclideanSpace ℝ (Fin 3)`.

* `solidCone S` is the cone over a subset `S` of the unit sphere.
* `sphericalArea S = 3 * volume (solidCone S)`; this is the usual surface area
  (for `S` the whole sphere it gives `4 * π`, see `sphericalArea_sphere`).
* `sphericalTriangle A B C` is the geodesic triangle with vertices `A`, `B`, `C`.
* `sphericalAngle A B C` is the interior angle at the vertex `A`.
-/

namespace Math

open MeasureTheory Metric Real
open scoped RealInnerProductSpace

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The cone with apex the origin over a subset of the unit sphere. -/
def solidCone (S : Set E3) : Set E3 :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ y ∈ S, x = t • y}

/-- The area of a region of the unit sphere, defined as three times the volume of the
cone over it.  (The cone over a region of area `a` on the unit sphere has volume `a / 3`.) -/
noncomputable def sphericalArea (S : Set E3) : ℝ :=
  3 * (volume (solidCone S)).toReal

/-- The geodesic (spherical) triangle with vertices `A`, `B`, `C`: the points of the unit
sphere lying in the cone positively spanned by `A`, `B`, `C`. -/
def sphericalTriangle (A B C : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C}

/-- The interior angle of the spherical triangle `A B C` at the vertex `A`: the angle between
the tangent directions at `A` of the two sides through `A`. -/
noncomputable def sphericalAngle (A B C : E3) : ℝ :=
  InnerProductGeometry.angle (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)

/-- `normalTo A B C` is the component of `C` orthogonal to the plane spanned by `A` and `B`
(for unit `A`); it is orthogonal to `A` and `B` and has positive inner product with `C`. -/
noncomputable def normalTo (A B C : E3) : E3 :=
  (C - ⟪A, C⟫ • A) - (⟪C - ⟪A, C⟫ • A, B - ⟪A, B⟫ • A⟫ / ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫) •
    (B - ⟪A, B⟫ • A)

end Math

import RequestProject.Defs

/-!
# Normals to the sides of a spherical triangle, and the dihedral angle identity
-/

namespace Math

open MeasureTheory Metric Real Module InnerProductGeometry
open scoped RealInnerProductSpace

/-- A convenient form of linear independence for three vectors. -/
def Indep3 (A B C : E3) : Prop :=
  ∀ a b c : ℝ, a • A + b • B + c • C = 0 → a = 0 ∧ b = 0 ∧ c = 0

lemma indep3_of_linearIndependent {A B C : E3} (h : LinearIndependent ℝ ![A, B, C]) :
    Indep3 A B C := by
  intro a b c habc
  rw [Fintype.linearIndependent_iff] at h
  have hz := h ![a, b, c] (by simpa [Fin.sum_univ_three] using habc)
  exact ⟨by simpa using hz 0, by simpa using hz 1, by simpa using hz 2⟩

/-- Three linearly independent vectors span `E3`. -/
lemma exists_repr {A B C : E3} (h : LinearIndependent ℝ ![A, B, C]) (x : E3) :
    ∃ a b c : ℝ, x = a • A + b • B + c • C := by
  have hcard : Fintype.card (Fin 3) = finrank ℝ E3 := by simp
  let b := basisOfLinearIndependentOfCardEqFinrank h hcard
  have hb : ⇑b = ![A, B, C] := coe_basisOfLinearIndependentOfCardEqFinrank h hcard
  refine ⟨b.repr x 0, b.repr x 1, b.repr x 2, ?_⟩
  have hsum := b.sum_repr x
  rw [Fin.sum_univ_three, hb] at hsum
  simpa using hsum.symm

lemma Indep3.perm₁ {A B C : E3} (h : Indep3 A B C) : Indep3 B A C := by
  intro a b c habc
  obtain ⟨h1, h2, h3⟩ := h b a c (by rw [← habc]; module)
  exact ⟨h2, h1, h3⟩

lemma Indep3.perm₂ {A B C : E3} (h : Indep3 A B C) : Indep3 A C B := by
  intro a b c habc
  obtain ⟨h1, h2, h3⟩ := h a c b (by rw [← habc]; module)
  exact ⟨h1, h3, h2⟩

lemma Indep3.rot {A B C : E3} (h : Indep3 A B C) : Indep3 B C A := by
  intro a b c habc
  obtain ⟨h1, h2, h3⟩ := h c a b (by rw [← habc]; module)
  exact ⟨h2, h3, h1⟩

/-! ### Two auxiliary facts about a pair of vectors -/

/-- The Gram determinant of two vectors, one nonzero and not parallel, is positive. -/
lemma inner_gram_pos {u v : E3} (hu : u ≠ 0) (hnp : ∀ r : ℝ, v ≠ r • u) :
    0 < ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  have hU : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  set k : ℝ := ⟪u, v⟫ / ⟪u, u⟫ with hk
  have hw : v - k • u ≠ 0 := fun h => hnp k (by rw [← sub_eq_zero]; exact h)
  have hpos := real_inner_self_pos.mpr hw
  have key : ⟪v - k • u, v - k • u⟫ = ⟪v, v⟫ - ⟪u, v⟫ ^ 2 / ⟪u, u⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm v u, hk]
    field_simp
    ring
  rw [key] at hpos
  have hmul : 0 < (⟪v, v⟫ - ⟪u, v⟫ ^ 2 / ⟪u, u⟫) * ⟪u, u⟫ := mul_pos hpos hU
  field_simp at hmul
  nlinarith [hmul]

/-- The two "projected" vectors make an angle supplementary to the angle between `u` and `v`. -/
lemma angle_proj_proj {u v : E3} (hu : u ≠ 0) (hv : v ≠ 0)
    (hD : 0 < ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2) :
    angle (u - (⟪u, v⟫ / ⟪v, v⟫) • v) (v - (⟪v, u⟫ / ⟪u, u⟫) • u) = π - angle u v := by
  have hU : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hV : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv
  have hvu : ⟪v, u⟫ = ⟪u, v⟫ := (real_inner_comm v u).symm
  rw [hvu]
  set U := ⟪u, u⟫ with hUdef
  set V := ⟪v, v⟫ with hVdef
  set p := ⟪u, v⟫ with hpdef
  set D := U * V - p ^ 2 with hDdef
  set X := u - (p / V) • v with hX
  set Y := v - (p / U) • u with hY
  have hXY : ⟪X, Y⟫ = -(p * D) / (U * V) := by
    simp only [hX, hY, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvu, ← hUdef, ← hVdef, ← hpdef, hDdef]
    field_simp
    ring
  have hXX : ⟪X, X⟫ = D / V := by
    simp only [hX, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvu, ← hUdef, ← hVdef, ← hpdef, hDdef]
    field_simp
    ring
  have hYY : ⟪Y, Y⟫ = D / U := by
    simp only [hY, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvu, ← hUdef, ← hVdef, ← hpdef, hDdef]
    field_simp
    ring
  have hg : (0:ℝ) < √(U * V) := Real.sqrt_pos.mpr (by positivity)
  have hg2 : √(U * V) ^ 2 = U * V := Real.sq_sqrt (by positivity)
  have hnX : ‖X‖ = √(D / V) := by rw [← hXX]; exact norm_eq_sqrt_real_inner X
  have hnY : ‖Y‖ = √(D / U) := by rw [← hYY]; exact norm_eq_sqrt_real_inner Y
  have hnu : ‖u‖ = √U := norm_eq_sqrt_real_inner u
  have hnv : ‖v‖ = √V := norm_eq_sqrt_real_inner v
  have hprod : ‖X‖ * ‖Y‖ = D / √(U * V) := by
    rw [hnX, hnY, ← Real.sqrt_mul (by positivity)]
    have h1 : D / V * (D / U) = (D / √(U * V)) ^ 2 := by
      rw [div_pow, hg2]; field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  have hprod2 : ‖u‖ * ‖v‖ = √(U * V) := by rw [hnu, hnv, ← Real.sqrt_mul (by positivity)]
  rw [angle, angle, hXY, hprod, hprod2]
  have hfin : ∀ g : ℝ, 0 < g → g ^ 2 = U * V → -(p * D) / (U * V) / (D / g) = -(p / g) := by
    intro g _ hgsq
    rw [← hgsq]
    field_simp
  rw [hfin _ hg hg2]
  exact Real.arccos_neg _

/-! ### The side normals of a spherical triangle -/

section

variable {A B C : E3}

/-- The tangent direction at `A` towards `B` is nonzero. -/
lemma tangent_ne_zero (h : Indep3 A B C) : B - ⟪A, B⟫ • A ≠ 0 := by
  intro h0
  have key : ⟪A, B⟫ • A + (-1 : ℝ) • B + (0 : ℝ) • C = -(B - ⟪A, B⟫ • A) := by module
  rw [h0, neg_zero] at key
  have := (h _ _ _ key).2.1
  norm_num at this

/-- The two tangent directions at `A` are not parallel. -/
lemma tangent_not_parallel (h : Indep3 A B C) (r : ℝ) :
    C - ⟪A, C⟫ • A ≠ r • (B - ⟪A, B⟫ • A) := by
  intro h0
  have key : (r * ⟪A, B⟫ - ⟪A, C⟫) • A + (-r) • B + (1 : ℝ) • C
      = (C - ⟪A, C⟫ • A) - r • (B - ⟪A, B⟫ • A) := by module
  rw [h0, sub_self] at key
  have := (h _ _ _ key).2.2
  norm_num at this

lemma inner_self_of_norm_one (hA : ‖A‖ = 1) : ⟪A, A⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hA]; norm_num

lemma inner_tangent_left (hA : ‖A‖ = 1) : ⟪B - ⟪A, B⟫ • A, A⟫ = 0 := by
  rw [inner_sub_left, real_inner_smul_left, inner_self_of_norm_one hA, real_inner_comm B A]
  ring

lemma normalTo_inner_fst (hA : ‖A‖ = 1) : ⟪normalTo A B C, A⟫ = 0 := by
  rw [normalTo, inner_sub_left, real_inner_smul_left, inner_tangent_left hA,
    inner_tangent_left hA]
  ring

lemma normalTo_inner_tangent (h : Indep3 A B C) :
    ⟪normalTo A B C, B - ⟪A, B⟫ • A⟫ = 0 := by
  have hu : B - ⟪A, B⟫ • A ≠ 0 := tangent_ne_zero h
  have huu : ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫ ≠ 0 :=
    ne_of_gt (real_inner_self_pos.mpr hu)
  rw [normalTo, inner_sub_left, real_inner_smul_left]
  field_simp
  ring

lemma normalTo_inner_snd (hA : ‖A‖ = 1) (h : Indep3 A B C) : ⟪normalTo A B C, B⟫ = 0 := by
  have hB : ⟪normalTo A B C, B⟫
      = ⟪normalTo A B C, (B - ⟪A, B⟫ • A) + ⟪A, B⟫ • A⟫ := by congr 1; module
  rw [hB, inner_add_right, real_inner_smul_right, normalTo_inner_fst hA,
    normalTo_inner_tangent h]
  ring

lemma normalTo_inner_trd (hA : ‖A‖ = 1) (h : Indep3 A B C) :
    ⟪normalTo A B C, C⟫ = ⟪normalTo A B C, normalTo A B C⟫ := by
  have hC : ⟪normalTo A B C, C⟫
      = ⟪normalTo A B C, (C - ⟪A, C⟫ • A) + ⟪A, C⟫ • A⟫ := by congr 1; module
  have h1 : ⟪normalTo A B C, C⟫ = ⟪normalTo A B C, C - ⟪A, C⟫ • A⟫ := by
    rw [hC, inner_add_right, real_inner_smul_right, normalTo_inner_fst hA]
    ring
  have h2 : ⟪normalTo A B C, normalTo A B C⟫ = ⟪normalTo A B C, C - ⟪A, C⟫ • A⟫ := by
    nth_rewrite 2 [normalTo]
    rw [inner_sub_right, real_inner_smul_right, normalTo_inner_tangent h]
    ring
  rw [h1, h2]

lemma normalTo_ne_zero (h : Indep3 A B C) : normalTo A B C ≠ 0 := by
  intro h0
  rw [normalTo, sub_eq_zero] at h0
  exact tangent_not_parallel h _ h0

/-- The normal to the plane through `A` and `B` on the side of `C` does not depend on the
order of `A` and `B`. -/
lemma normalTo_symm (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (h : Indep3 A B C) :
    normalTo A B C = normalTo B A C := by
  set N1 := normalTo A B C with hN1
  set N2 := normalTo B A C with hN2
  have hspan : ∃ s t : ℝ, N1 - N2 = s • A + t • B := by
    refine ⟨(⟪C - ⟪A, C⟫ • A, B - ⟪A, B⟫ • A⟫ / ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫) * ⟪A, B⟫
        - ⟪A, C⟫ + (⟪C - ⟪B, C⟫ • B, A - ⟪B, A⟫ • B⟫ / ⟪A - ⟪B, A⟫ • B, A - ⟪B, A⟫ • B⟫),
      ⟪B, C⟫ - (⟪C - ⟪A, C⟫ • A, B - ⟪A, B⟫ • A⟫ / ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫)
        - (⟪C - ⟪B, C⟫ • B, A - ⟪B, A⟫ • B⟫ / ⟪A - ⟪B, A⟫ • B, A - ⟪B, A⟫ • B⟫) * ⟪B, A⟫, ?_⟩
    rw [hN1, hN2, normalTo, normalTo]
    module
  obtain ⟨s, t, hst⟩ := hspan
  have hA1 : ⟪N1 - N2, A⟫ = 0 := by
    rw [inner_sub_left, normalTo_inner_fst hA, normalTo_inner_snd hB h.perm₁]
    ring
  have hB1 : ⟪N1 - N2, B⟫ = 0 := by
    rw [inner_sub_left, normalTo_inner_snd hA h, normalTo_inner_fst hB]
    ring
  have : ⟪N1 - N2, N1 - N2⟫ = 0 := by
    nth_rewrite 2 [hst]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hA1, hB1]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp this)

lemma sphericalAngle_pos (h : Indep3 A B C) : 0 < sphericalAngle A B C := by
  rcases lt_or_eq_of_le (angle_nonneg (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)) with h' | h'
  · exact h'
  · exfalso
    rw [eq_comm, angle_eq_zero_iff] at h'
    obtain ⟨-, r, -, hr⟩ := h'
    exact tangent_not_parallel h r hr

lemma sphericalAngle_lt_pi (h : Indep3 A B C) : sphericalAngle A B C < π := by
  rcases lt_or_eq_of_le (angle_le_pi (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)) with h' | h'
  · exact h'
  · exfalso
    rw [angle_eq_pi_iff] at h'
    obtain ⟨-, r, -, hr⟩ := h'
    exact tangent_not_parallel h r hr

/-- The angle between the two side normals at the vertex `A` is supplementary to the
interior angle of the triangle at `A`. -/
lemma angle_normalTo (h : Indep3 A B C) :
    angle (normalTo A C B) (normalTo A B C) = π - sphericalAngle A B C := by
  have hu : B - ⟪A, B⟫ • A ≠ 0 := tangent_ne_zero h
  have hv : C - ⟪A, C⟫ • A ≠ 0 := tangent_ne_zero h.perm₂
  have hD := inner_gram_pos hu (tangent_not_parallel h)
  have := angle_proj_proj hu hv hD
  rw [sphericalAngle]
  rw [← this]
  rfl

end

end Math

import Mathlib
import RequestProject.Angles
import RequestProject.Octants

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Math

open MeasureTheory Metric Real Set InnerProductGeometry
open scoped RealInnerProductSpace ENNReal

/-- The cone over the whole unit sphere is the closed unit ball, so the sphere has area
`4 * π`: the normalisation of `sphericalArea` is the usual one. -/
lemma sphericalArea_sphere : sphericalArea {x : E3 | ‖x‖ = 1} = 4 * π := by
  have hcone : solidCone {x : E3 | ‖x‖ = 1} = closedBall (0 : E3) 1 := by
    ext x
    simp only [solidCone, mem_setOf_eq, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨t, ht0, ht1, y, hy, rfl⟩
      rw [norm_smul, show ‖y‖ = 1 from hy, Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
      exact ht1
    · intro hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨0, le_refl _, zero_le_one, EuclideanSpace.single 0 1, by
          simp [EuclideanSpace.norm_single], by simp⟩
      · refine ⟨‖x‖, norm_nonneg _, hx, ‖x‖⁻¹ • x, ?_, ?_⟩
        · simp only [norm_smul, norm_inv, norm_norm]
          field_simp
        · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]
  rw [sphericalArea, hcone, volume_closedBall_E3,
    ENNReal.toReal_ofReal (by positivity)]
  ring

section

variable {A B C : E3}

/-- The cone over the spherical triangle is the intersection of the unit ball with the three
half-spaces determined by the side normals. -/
lemma solidCone_triangle (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hind : LinearIndependent ℝ ![A, B, C]) :
    solidCone (sphericalTriangle A B C)
      = Oct3 (normalTo B C A) (normalTo C A B) (normalTo A B C) 1 1 1 := by
  have h3 : Indep3 A B C := indep3_of_linearIndependent hind
  set nA := normalTo B C A with hnAdef
  set nB := normalTo C A B with hnBdef
  set nC := normalTo A B C with hnCdef
  have hAnA : ⟪A, nA⟫ = ⟪nA, nA⟫ := by
    rw [real_inner_comm]; exact normalTo_inner_trd hB h3.rot
  have hBnA : ⟪B, nA⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_fst hB
  have hCnA : ⟪C, nA⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_snd hB h3.rot
  have hBnB : ⟪B, nB⟫ = ⟪nB, nB⟫ := by
    rw [real_inner_comm]; exact normalTo_inner_trd hC h3.rot.rot
  have hCnB : ⟪C, nB⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_fst hC
  have hAnB : ⟪A, nB⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_snd hC h3.rot.rot
  have hCnC : ⟪C, nC⟫ = ⟪nC, nC⟫ := by rw [real_inner_comm]; exact normalTo_inner_trd hA h3
  have hAnC : ⟪A, nC⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_fst hA
  have hBnC : ⟪B, nC⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_snd hA h3
  have pA : 0 < ⟪nA, nA⟫ := real_inner_self_pos.mpr (normalTo_ne_zero h3.rot)
  have pB : 0 < ⟪nB, nB⟫ := real_inner_self_pos.mpr (normalTo_ne_zero h3.rot.rot)
  have pC : 0 < ⟪nC, nC⟫ := real_inner_self_pos.mpr (normalTo_ne_zero h3)
  have expA : ∀ a b c : ℝ, ⟪a • A + b • B + c • C, nA⟫ = a * ⟪nA, nA⟫ := by
    intro a b c
    simp only [inner_add_left, real_inner_smul_left, hAnA, hBnA, hCnA]
    ring
  have expB : ∀ a b c : ℝ, ⟪a • A + b • B + c • C, nB⟫ = b * ⟪nB, nB⟫ := by
    intro a b c
    simp only [inner_add_left, real_inner_smul_left, hAnB, hBnB, hCnB]
    ring
  have expC : ∀ a b c : ℝ, ⟪a • A + b • B + c • C, nC⟫ = c * ⟪nC, nC⟫ := by
    intro a b c
    simp only [inner_add_left, real_inner_smul_left, hAnC, hBnC, hCnC]
    ring
  ext x
  simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul, solidCone,
    sphericalTriangle]
  constructor
  · rintro ⟨t, ht0, ht1, y, ⟨hy1, a, b, c, ha, hb, hc, rfl⟩, rfl⟩
    have hnorm : ‖t • (a • A + b • B + c • C)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hy1, mul_one]
      exact ht1
    refine ⟨⟨⟨hnorm, ?_⟩, ?_⟩, ?_⟩
    · rw [real_inner_smul_left, expA]
      positivity
    · rw [real_inner_smul_left, expB]
      positivity
    · rw [real_inner_smul_left, expC]
      positivity
  · rintro ⟨⟨⟨hnorm, h1⟩, h2⟩, h3'⟩
    obtain ⟨a, b, c, rfl⟩ := exists_repr hind x
    rw [expA] at h1
    rw [expB] at h2
    rw [expC] at h3'
    have ha : 0 ≤ a := nonneg_of_mul_nonneg_left h1 pA
    have hb : 0 ≤ b := nonneg_of_mul_nonneg_left h2 pB
    have hc : 0 ≤ c := nonneg_of_mul_nonneg_left h3' pC
    rcases eq_or_ne (a • A + b • B + c • C) 0 with hx0 | hx0
    · refine ⟨0, le_refl _, zero_le_one, A, ⟨hA, 1, 0, 0, zero_le_one, le_refl _, le_refl _,
        by module⟩, ?_⟩
      rw [hx0, zero_smul]
    · refine ⟨‖a • A + b • B + c • C‖, norm_nonneg _, hnorm,
        ‖a • A + b • B + c • C‖⁻¹ • (a • A + b • B + c • C), ⟨?_, ?_⟩, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm]
        field_simp
      · refine ⟨‖a • A + b • B + c • C‖⁻¹ * a, ‖a • A + b • B + c • C‖⁻¹ * b,
          ‖a • A + b • B + c • C‖⁻¹ * c, ?_, ?_, ?_, by module⟩
        · positivity
        · positivity
        · positivity
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]

end

/-- **Girard's theorem / Gauss–Bonnet for a spherical triangle.**
The angle sum of a (nondegenerate) geodesic triangle on the unit sphere exceeds `π`
exactly by the area of the triangle. -/
theorem gauss_bonnet_polygon (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hind : LinearIndependent ℝ ![A, B, C]) :
    sphericalAngle A B C + sphericalAngle B C A + sphericalAngle C A B - π
      = sphericalArea (sphericalTriangle A B C) := by
  have h3 : Indep3 A B C := indep3_of_linearIndependent hind
  set nA := normalTo B C A with hnAdef
  set nB := normalTo C A B with hnBdef
  set nC := normalTo A B C with hnCdef
  have hnA : nA ≠ 0 := normalTo_ne_zero h3.rot
  have hnB : nB ≠ 0 := normalTo_ne_zero h3.rot.rot
  have hnC : nC ≠ 0 := normalTo_ne_zero h3
  set α := sphericalAngle A B C with hα
  set β := sphericalAngle B C A with hβ
  set γ := sphericalAngle C A B with hγ
  -- the three interior angles lie in `(0, π)`
  have hα0 : 0 < α := sphericalAngle_pos h3
  have hαπ : α < π := sphericalAngle_lt_pi h3
  have hβ0 : 0 < β := sphericalAngle_pos h3.rot
  have hβπ : β < π := sphericalAngle_lt_pi h3.rot
  have hγ0 : 0 < γ := sphericalAngle_pos h3.rot.rot
  have hγπ : γ < π := sphericalAngle_lt_pi h3.rot.rot
  -- the angles between the normals
  have hangA : angle nB nC = π - α := by
    rw [hnBdef, ← normalTo_symm hA hC h3.perm₂]
    exact angle_normalTo h3
  have hangB : angle nC nA = π - β := by
    rw [hnCdef, ← normalTo_symm hB hA h3.perm₁]
    exact angle_normalTo h3.rot
  have hangC : angle nA nB = π - γ := by
    rw [hnAdef, ← normalTo_symm hC hB h3.rot.rot.perm₂]
    exact angle_normalTo h3.rot.rot
  -- volumes of the three wedges
  have hwA : volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫}
      = ENNReal.ofReal (2 * α / 3) := by
    rw [volume_wedge nB nC hnB hnC (by rw [hangA]; linarith) (by rw [hangA]; linarith), hangA]
    ring_nf
  have hwB : volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nC⟫}
      = ENNReal.ofReal (2 * β / 3) := by
    have h' : angle nA nC = π - β := by rw [angle_comm]; exact hangB
    rw [volume_wedge nA nC hnA hnC (by rw [h']; linarith) (by rw [h']; linarith), h']
    ring_nf
  have hwC : volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫}
      = ENNReal.ofReal (2 * γ / 3) := by
    rw [volume_wedge nA nB hnA hnB (by rw [hangC]; linarith) (by rw [hangC]; linarith), hangC]
    ring_nf
  -- pass to real numbers
  set V : ℝ → ℝ → ℝ → ℝ := fun s t u => (volume (Oct3 nA nB nC s t u)).toReal with hV
  have key : ∀ {X Y Z : Set E3}, Y ⊆ unitBall3 → Z ⊆ unitBall3 →
      volume X = volume Y + volume Z →
      (volume X).toReal = (volume Y).toReal + (volume Z).toReal := by
    intro X Y Z hY hZ h
    rw [h, ENNReal.toReal_add (volume_ne_top_of_subset hY) (volume_ne_top_of_subset hZ)]
  -- the eight octants exhaust the ball
  have e0 : (volume unitBall3).toReal = 4 * π / 3 := by
    rw [volume_unitBall3, ENNReal.toReal_ofReal (by positivity)]
  have s1 : (volume unitBall3).toReal
      = (volume (Oct1 nA 1)).toReal + (volume (Oct1 nA (-1))).toReal :=
    key (Oct1_subset nA 1) (Oct1_subset nA (-1)) (volume_split_ball hnA)
  have s2 : ∀ s : ℝ, (volume (Oct1 nA s)).toReal
      = (volume (Oct2 nA nB s 1)).toReal + (volume (Oct2 nA nB s (-1))).toReal := fun s =>
    key (Oct2_subset nA nB s 1) (Oct2_subset nA nB s (-1)) (volume_split_Oct1 hnB s)
  have s3 : ∀ s t : ℝ, (volume (Oct2 nA nB s t)).toReal = V s t 1 + V s t (-1) := fun s t =>
    key (Oct3_subset nA nB nC s t 1) (Oct3_subset nA nB nC s t (-1)) (volume_split_Oct2 hnC s t)
  -- the wedges split into two octants each
  have wA : 2 * α / 3 = V 1 1 1 + V (-1) 1 1 := by
    have := key (Oct3_subset nA nB nC 1 1 1) (Oct3_subset nA nB nC (-1) 1 1)
      (volume_wedgeA_split (nB := nB) (nC := nC) hnA)
    rw [hwA, ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  have wB : 2 * β / 3 = V 1 1 1 + V 1 (-1) 1 := by
    have := key (Oct3_subset nA nB nC 1 1 1) (Oct3_subset nA nB nC 1 (-1) 1)
      (volume_wedgeB_split (nA := nA) (nC := nC) hnB)
    rw [hwB, ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  have wC : 2 * γ / 3 = V 1 1 1 + V 1 1 (-1) := by
    have := key (Oct3_subset nA nB nC 1 1 1) (Oct3_subset nA nB nC 1 1 (-1))
      (volume_wedgeC_split (nA := nA) (nB := nB) hnC)
    rw [hwC, ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  -- antipodal symmetry
  have n1 : V (-1) (-1) (-1) = V 1 1 1 := by
    simpa [hV] using congrArg ENNReal.toReal (volume_Oct3_neg nA nB nC 1 1 1)
  have n2 : V 1 (-1) (-1) = V (-1) 1 1 := by
    simpa [hV] using congrArg ENNReal.toReal (volume_Oct3_neg nA nB nC (-1) 1 1)
  have n3 : V (-1) 1 (-1) = V 1 (-1) 1 := by
    simpa [hV] using congrArg ENNReal.toReal (volume_Oct3_neg nA nB nC 1 (-1) 1)
  have n4 : V (-1) (-1) 1 = V 1 1 (-1) := by
    simpa [hV] using congrArg ENNReal.toReal (volume_Oct3_neg nA nB nC 1 1 (-1))
  -- put everything together
  have harea : sphericalArea (sphericalTriangle A B C) = 3 * V 1 1 1 := by
    rw [sphericalArea, solidCone_triangle hA hB hC hind]
  rw [harea]
  have h21 := s2 1
  have h22 := s2 (-1)
  have h311 := s3 1 1
  have h31m := s3 1 (-1)
  have h3m1 := s3 (-1) 1
  have h3mm := s3 (-1) (-1)
  rw [e0] at s1
  linarith [s1, h21, h22, h311, h31m, h3m1, h3mm, wA, wB, wC, n1, n2, n3, n4]

end Math

