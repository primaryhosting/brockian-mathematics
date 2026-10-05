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

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/
lemma integrable_continuousMap (f : C(Circ, ℂ)) (μ : Measure Circ) [IsFiniteMeasure μ] :
    Integrable f μ :=
  (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- For a probability measure, integration is a contraction for the sup norm. -/
lemma norm_integral_sub_le (μ : Measure Circ) [IsProbabilityMeasure μ] (f g : C(Circ, ℂ)) :
    ‖(∫ t, f t ∂μ) - ∫ t, g t ∂μ‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_continuousMap f μ) (integrable_continuousMap g μ)]
  have h : ∀ t : Circ, ‖f t - g t‖ ≤ ‖f - g‖ := by
    intro t
    have := ContinuousMap.norm_coe_le_norm (f - g) t
    simpa using this
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖f - g‖)
    (f := fun t => f t - g t) (Filter.Eventually.of_forall h)
  simpa using this

/-! ### The empirical measures -/

/-- The empirical measure of the first `N + 1` terms of a sequence in the circle. -/
noncomputable def emp (x : ℕ → Circ) (N : ℕ) : Measure Circ :=
  ((N : ℝ≥0∞) + 1)⁻¹ • ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n)

instance instIsProbEmp (x : ℕ → Circ) (N : ℕ) : IsProbabilityMeasure (emp x N) := by
  constructor
  simp only [emp, Measure.smul_apply, Measure.finset_sum_apply, measure_univ, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.inv_mul_cancel (by positivity) (by simp)]

/-- The empirical measure, packaged as a probability measure. -/
noncomputable def empProb (x : ℕ → Circ) (N : ℕ) : ProbabilityMeasure Circ :=
  ⟨emp x N, inferInstance⟩

lemma integral_emp (x : ℕ → Circ) (N : ℕ) (f : Circ → ℂ) (hf : Continuous f) :
    ∫ t, f t ∂(emp x N) = ((N : ℂ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), f (x n) := by
  rw [emp, integral_smul_measure, integral_finset_sum_measure
    (fun n _ => (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)))]
  simp only [integral_dirac]
  rw [ENNReal.toReal_inv, Complex.real_smul]
  norm_num
  ring_nf
  left
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp

open scoped Classical in
lemma emp_apply (x : ℕ → Circ) (N : ℕ) {E : Set Circ} (hE : MeasurableSet E) :
    (emp x N) E =
      ((N : ℝ≥0∞) + 1)⁻¹ * (((Finset.range (N + 1)).filter (fun n => x n ∈ E)).card : ℝ≥0∞) := by
  simp only [emp, Measure.smul_apply, Measure.finset_sum_apply, Measure.dirac_apply' _ hE,
    smul_eq_mul, Set.indicator_apply, Pi.one_apply]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : x n ∈ E <;> simp [h]

/-! ### Weyl's criterion -/

lemma integral_fourier_eq_zero {h : ℤ} (hh : h ≠ 0) :
    ∫ t, (fourier h : C(Circ, ℂ)) t ∂(volume : Measure Circ) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (g := ((1 / 2 / h : ℝ) : Circ))
    (fun t => fourier_add_half_inv_index hh one_pos t)

/-- The property that the empirical averages of `f` converge to its integral. -/
def GoodFun (x : ℕ → Circ) (f : C(Circ, ℂ)) : Prop :=
  Tendsto (fun N : ℕ => ∫ t, f t ∂(emp x N)) atTop (𝓝 (∫ t, f t ∂(volume : Measure Circ)))

/-- The continuous functions whose empirical averages converge to their integral form a
linear subspace of `C(Circ, ℂ)`. -/
noncomputable def goodFuns (x : ℕ → Circ) : Submodule ℂ C(Circ, ℂ) where
  carrier := {f | GoodFun x f}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, GoodFun]
    simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, GoodFun] at *
    have h1 : ∀ N : ℕ, ∫ t, (f + g) t ∂(emp x N)
        = (∫ t, f t ∂(emp x N)) + ∫ t, g t ∂(emp x N) := by
      intro N
      simpa using integral_add (integrable_continuousMap f (emp x N))
        (integrable_continuousMap g (emp x N))
    have h2 : ∫ t, (f + g) t ∂(volume : Measure Circ)
        = (∫ t, f t ∂(volume : Measure Circ)) + ∫ t, g t ∂(volume : Measure Circ) := by
      simpa using integral_add (integrable_continuousMap f volume)
        (integrable_continuousMap g volume)
    simp only [h1, h2]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, GoodFun] at *
    have h1 : ∀ N : ℕ, ∫ t, (c • f) t ∂(emp x N) = c * ∫ t, f t ∂(emp x N) := by
      intro N
      simpa [smul_eq_mul] using integral_smul (μ := emp x N) c (fun t => f t)
    have h2 : ∫ t, (c • f) t ∂(volume : Measure Circ)
        = c * ∫ t, f t ∂(volume : Measure Circ) := by
      simpa [smul_eq_mul] using integral_smul (μ := (volume : Measure Circ)) c (fun t => f t)
    simp only [h1, h2]
    exact hf.const_mul c

lemma mem_goodFuns {x : ℕ → Circ} {f : C(Circ, ℂ)} : f ∈ goodFuns x ↔ GoodFun x f := Iff.rfl

/-- Weyl's criterion, functional form: if all nontrivial exponential averages tend to zero, then
the averages of any continuous function tend to its integral. -/
lemma tendsto_integral_of_weyl (x : ℕ → Circ)
    (hW : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => ∫ t, (fourier h : C(Circ, ℂ)) t ∂(emp x N)) atTop (𝓝 0))
    (f : C(Circ, ℂ)) :
    Tendsto (fun N : ℕ => ∫ t, f t ∂(emp x N)) atTop
      (𝓝 (∫ t, f t ∂(volume : Measure Circ))) := by
  -- the span of the Fourier monomials consists of good functions
  have hspan : (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) ≤ goodFuns x := by
    rw [Submodule.span_le]
    rintro - ⟨n, rfl⟩
    rw [SetLike.mem_coe, mem_goodFuns, GoodFun]
    rcases eq_or_ne n 0 with rfl | hn
    · have h0 : ∀ μ : Measure Circ, IsProbabilityMeasure μ →
          ∫ t, (fourier (0 : ℤ) : C(Circ, ℂ)) t ∂μ = 1 := by
        intro μ hμ
        simp
      simp only [h0 _ (instIsProbEmp x _), h0 _ inferInstance]
      exact tendsto_const_nhds
    · rw [integral_fourier_eq_zero hn]
      exact hW n hn
  -- and the span is dense
  have hfmem : f ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) : Set _) := by
    have : (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure = ⊤ :=
      span_fourier_closure_eq_top
    have hmem : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
      rw [this]; trivial
    exact hmem
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hg⟩ := Metric.mem_closure_iff.mp hfmem (ε / 3) (by positivity)
  have hgood : GoodFun x g := hspan hgmem
  rw [GoodFun, Metric.tendsto_atTop] at hgood
  obtain ⟨N₀, hN₀⟩ := hgood (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hfg : ‖f - g‖ < ε / 3 := by
    rw [dist_eq_norm] at hg
    exact hg
  have h1 : ‖(∫ t, f t ∂(emp x N)) - ∫ t, g t ∂(emp x N)‖ ≤ ‖f - g‖ :=
    norm_integral_sub_le _ f g
  have h2 : ‖(∫ t, g t ∂(volume : Measure Circ)) - ∫ t, f t ∂(volume : Measure Circ)‖ ≤ ‖f - g‖ := by
    have := norm_integral_sub_le (volume : Measure Circ) g f
    rwa [show ‖g - f‖ = ‖f - g‖ from norm_sub_rev g f] at this
  have h3 : dist (∫ t, g t ∂(emp x N)) (∫ t, g t ∂(volume : Measure Circ)) < ε / 3 := hN₀ N hN
  rw [dist_eq_norm] at h3 ⊢
  calc ‖(∫ t, f t ∂(emp x N)) - ∫ t, f t ∂(volume : Measure Circ)‖
      = ‖((∫ t, f t ∂(emp x N)) - ∫ t, g t ∂(emp x N)) +
          (((∫ t, g t ∂(emp x N)) - ∫ t, g t ∂(volume : Measure Circ)) +
            ((∫ t, g t ∂(volume : Measure Circ)) - ∫ t, f t ∂(volume : Measure Circ)))‖ := by
        ring_nf
    _ ≤ ‖(∫ t, f t ∂(emp x N)) - ∫ t, g t ∂(emp x N)‖ +
          (‖(∫ t, g t ∂(emp x N)) - ∫ t, g t ∂(volume : Measure Circ)‖ +
            ‖(∫ t, g t ∂(volume : Measure Circ)) - ∫ t, f t ∂(volume : Measure Circ)‖) :=
        le_trans (norm_add_le _ _) (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

/-- Weak convergence of the empirical measures to the Haar (Lebesgue) probability measure. -/
lemma tendsto_empProb (x : ℕ → Circ)
    (hW : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => ∫ t, (fourier h : C(Circ, ℂ)) t ∂(emp x N)) atTop (𝓝 0)) :
    Tendsto (empProb x) atTop
      (𝓝 (⟨(volume : Measure Circ), inferInstance⟩ : ProbabilityMeasure Circ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have := tendsto_integral_of_weyl x hW f.toContinuousMap
  simpa [empProb] using this

/-! ### Arcs and their measures -/

/-- The image in the circle of a half-open interval. -/
def arc (a b : ℝ) : Set Circ := (QuotientAddGroup.mk '' (Set.Ico a b))

/-- The class of a real number in the circle is the class of its fractional part. -/
lemma coe_fract (y : ℝ) : ((Int.fract y : ℝ) : Circ) = (y : Circ) := by
  rw [Int.fract, QuotientAddGroup.eq_iff_sub_mem]
  simp only [sub_sub_cancel_left]
  exact ⟨-⌊y⌋, by push_cast; ring⟩

lemma mem_arc_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (y : ℝ) :
    ((y : Circ) ∈ arc a b) ↔ Int.fract y ∈ Set.Ico a b := by
  constructor
  · rintro ⟨z, hz, hcoe⟩
    have hz01 : z ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      refine ⟨by linarith [hz.1], ?_⟩
      simpa using lt_of_lt_of_le hz.2 hb
    have hfy : Int.fract y ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg y, by simpa using Int.fract_lt_one y⟩
    have hcc : ((Int.fract y : ℝ) : Circ) = ((z : ℝ) : Circ) := by
      rw [coe_fract y, ← hcoe]
    have hz' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hfy hz01).mp hcc
    rw [hz']; exact hz
  · intro h
    exact ⟨Int.fract y, h, coe_fract y⟩

lemma volume_singleton_circ (p : Circ) : (volume : Measure Circ) ({p} : Set Circ) = 0 := by
  simpa using AddCircle.volume_closedBall (T := (1 : ℝ)) (x := p) 0

lemma isOpen_arcIoo (a b : ℝ) : IsOpen (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

lemma isClosed_arcIcc (a b : ℝ) : IsClosed (QuotientAddGroup.mk '' (Set.Icc a b) : Set Circ) :=
  ((isCompact_Icc).image (by continuity)).isClosed

lemma diff_subset_endpoints (a b : ℝ) :
    (QuotientAddGroup.mk '' (Set.Icc a b) : Set Circ) \ (QuotientAddGroup.mk '' (Set.Ioo a b))
      ⊆ {((a : ℝ) : Circ), ((b : ℝ) : Circ)} := by
  rintro p ⟨⟨t, ht, rfl⟩, hp⟩
  by_cases hta : t = a
  · left; rw [hta]
  by_cases htb : t = b
  · right; rw [htb]; rfl
  exact absurd ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩, rfl⟩ hp

lemma measurableSet_arc (a b : ℝ) : MeasurableSet (arc a b) := by
  have hU : MeasurableSet (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) :=
    (isOpen_arcIoo a b).measurableSet
  have hsub : (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) ⊆ arc a b :=
    Set.image_mono Set.Ioo_subset_Ico_self
  have hfin : (arc a b \ (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ)).Finite := by
    refine Set.Finite.subset
      (Set.toFinite ({((a : ℝ) : Circ), ((b : ℝ) : Circ)} : Set Circ)) ?_
    refine subset_trans (Set.diff_subset_diff_left (Set.image_mono Set.Ico_subset_Icc_self)) ?_
    exact diff_subset_endpoints a b
  have harc : arc a b = (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) ∪
      (arc a b \ (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ)) := by
    rw [Set.union_diff_cancel hsub]
  rw [harc]
  exact hU.union hfin.measurableSet

lemma volume_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (volume : Measure Circ) (arc a b) = ENNReal.ofReal (b - a) := by
  have hproj := AddCircle.add_projection_respects_measure 1 0 (measurableSet_arc a b)
  rw [zero_add] at hproj
  set S : Set ℝ := QuotientAddGroup.mk ⁻¹' (arc a b) ∩ Set.Ioc 0 1 with hS
  have hmem : ∀ y : ℝ, y ∈ S ↔ (Int.fract y ∈ Set.Ico a b ∧ y ∈ Set.Ioc (0 : ℝ) 1) := by
    intro y
    simp only [hS, Set.mem_inter_iff, Set.mem_preimage]
    rw [mem_arc_iff ha hb]
  have h1 : Set.Ioo a b ⊆ S := by
    intro y hy
    rw [hmem]
    have hy0 : 0 < y := lt_of_le_of_lt ha hy.1
    have hy1 : y < 1 := lt_of_lt_of_le hy.2 hb
    refine ⟨?_, ⟨hy0, le_of_lt hy1⟩⟩
    rw [Int.fract_eq_self.mpr ⟨le_of_lt hy0, hy1⟩]
    exact ⟨le_of_lt hy.1, hy.2⟩
  have h2 : S ⊆ Set.Icc a b ∪ {(1 : ℝ)} := by
    intro y hy
    rw [hmem] at hy
    obtain ⟨hf, hy0, hy1⟩ := hy
    rcases eq_or_lt_of_le hy1 with h | h
    · right; exact h
    · left
      rw [Int.fract_eq_self.mpr ⟨le_of_lt hy0, h⟩] at hf
      exact ⟨hf.1, le_of_lt hf.2⟩
  have hle1 : ENNReal.ofReal (b - a) ≤ (volume : Measure ℝ) S := by
    have h := measure_mono (μ := (volume : Measure ℝ)) h1
    rwa [Real.volume_Ioo] at h
  have hle2 : (volume : Measure ℝ) S ≤ ENNReal.ofReal (b - a) := by
    refine le_trans (measure_mono (μ := (volume : Measure ℝ)) h2) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [Real.volume_Icc, Real.volume_singleton, add_zero]
  rw [hproj]
  exact le_antisymm hle2 hle1

lemma volume_frontier_arc (a b : ℝ) :
    (volume : Measure Circ) (frontier (arc a b)) = 0 := by
  have hclosure : closure (arc a b) ⊆ (QuotientAddGroup.mk '' (Set.Icc a b) : Set Circ) :=
    closure_minimal (Set.image_mono Set.Ico_subset_Icc_self) (isClosed_arcIcc a b)
  have hint : (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) ⊆ interior (arc a b) :=
    interior_maximal (Set.image_mono Set.Ioo_subset_Ico_self) (isOpen_arcIoo a b)
  have hsub : frontier (arc a b) ⊆ {((a : ℝ) : Circ), ((b : ℝ) : Circ)} :=
    subset_trans (Set.diff_subset_diff hclosure hint) (diff_subset_endpoints a b)
  refine measure_mono_null hsub ?_
  rw [Set.insert_eq]
  exact measure_union_null (volume_singleton_circ _) (volume_singleton_circ _)

/-! ### The main theorem -/

/-- **Weyl's equidistribution theorem.**  If a real sequence `x` has the asymptotic property that
all its nontrivial exponential averages `(1/N) ∑_{n < N} e(h xₙ)` tend to `0`, then `x` is
equidistributed modulo one: for every subinterval `[a, b) ⊆ [0, 1]` the proportion of the first `N`
fractional parts lying in `[a, b)` tends to its length `b - a`. -/
theorem equidistribution_of_asymptotic_exists (x : ℕ → ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h * x n)) / (N : ℂ))
        atTop (𝓝 0))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter
          (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a)) := by
  classical
  set y : ℕ → Circ := fun n => ((x n : ℝ) : Circ) with hy
  -- Step 1: rewrite the hypothesis as a statement about the empirical measures
  have hW' : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => ∫ t, (fourier h : C(Circ, ℂ)) t ∂(emp y N)) atTop (𝓝 0) := by
    intro h hh
    have hshift := (hW h hh).comp (Filter.tendsto_add_atTop_nat 1)
    refine hshift.congr ?_
    intro N
    rw [integral_emp y N _ (map_continuous (fourier h))]
    have hval : ∀ n : ℕ, (fourier h : C(Circ, ℂ)) (y n)
        = Complex.exp (2 * π * Complex.I * h * x n) := by
      intro n
      rw [hy]
      simp [fourier_coe_apply (T := (1 : ℝ)) (n := h) (x := x n)]
    simp only [hval, Function.comp_apply]
    rw [div_eq_inv_mul]
    push_cast
    ring
  -- Step 2: weak convergence of the empirical measures
  have hweak := tendsto_empProb y hW'
  -- Step 3: portmanteau applied to the arc `[a, b)`
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μ := (⟨(volume : Measure Circ), inferInstance⟩ : ProbabilityMeasure Circ))
    (E := arc a b) hweak (by simpa using volume_frontier_arc a b)
  have hport' : Tendsto (fun N : ℕ => (emp y N) (arc a b)) atTop
      (𝓝 (ENNReal.ofReal (b - a))) := by
    rw [← volume_arc ha hb]
    exact hport
  -- Step 4: convert to real-valued proportions
  have htoReal := (ENNReal.tendsto_toReal (by simp)).comp hport'
  rw [ENNReal.toReal_ofReal (by linarith)] at htoReal
  have hcount : ∀ N : ℕ, ((emp y N) (arc a b)).toReal
      = (((Finset.range (N + 1)).filter
          (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) / ((N : ℝ) + 1) := by
    intro N
    rw [emp_apply y N (measurableSet_arc a b)]
    have hfilter : ((Finset.range (N + 1)).filter (fun n => y n ∈ arc a b))
        = ((Finset.range (N + 1)).filter
            (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) := by
      refine Finset.filter_congr ?_
      intro n _
      rw [hy]
      simpa [Set.mem_Ico] using mem_arc_iff ha hb (x n)
    rw [hfilter, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp [div_eq_inv_mul]
  have hfinal : Tendsto (fun N : ℕ =>
      (((Finset.range (N + 1)).filter
        (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) / ((N : ℝ) + 1))
      atTop (𝓝 (b - a)) := by
    refine htoReal.congr ?_
    intro N
    exact hcount N
  -- Step 5: undo the index shift
  refine (Filter.tendsto_add_atTop_iff_nat (f := fun N : ℕ =>
    (((Finset.range N).filter
      (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) / (N : ℝ)) 1).mp ?_
  refine hfinal.congr ?_
  intro N
  push_cast
  ring_nf

/-! ### An application: irrational rotations -/

/-- For irrational `α` and `h ≠ 0`, the exponential averages of the sequence `n ↦ n • α` tend to
zero: this is the geometric-series estimate underlying Weyl's theorem for irrational rotations. -/
lemma tendsto_exp_average_irrational (al : ℝ) (hal : Irrational al) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al))) / (N : ℂ))
      atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * π * Complex.I * h * al) with hzdef
  have hznorm : ‖z‖ = 1 := by
    rw [hzdef, Complex.norm_exp]
    norm_num
  have hz1 : z ≠ 1 := by
    rw [hzdef, Ne, Complex.exp_eq_one_iff]
    rintro ⟨k, hk⟩
    have h2pi : (2 : ℂ) * π * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hfac : ((h : ℂ) * al - k) * (2 * π * Complex.I) = 0 := by linear_combination hk
    have hk' : (h : ℂ) * al = (k : ℂ) := by
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact sub_eq_zero.mp h1
      · exact absurd h1 h2pi
    have hreal : (h : ℝ) * al = (k : ℝ) := by exact_mod_cast hk'
    have hh' : (h : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hh
    refine hal ⟨(k / h : ℚ), ?_⟩
    push_cast
    field_simp at hreal ⊢
    linarith [hreal]
  have hterm : ∀ n : ℕ, Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al)) = z ^ n := by
    intro n
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al)) = (z ^ N - 1) / (z - 1) := by
    intro N
    simp only [hterm]
    exact geom_sum_eq hz1 N
  have hzpos : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hbound : ∀ N : ℕ, ‖(∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al))) / (N : ℂ)‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    rw [hsum N, norm_div, norm_div, Complex.norm_natCast]
    have h2 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    gcongr
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- **Weyl's equidistribution theorem for irrational rotations.**  For irrational `al`, the
sequence `n ↦ n * al` is equidistributed modulo one. -/
theorem equidistribution_irrational_rotation (al : ℝ) (hal : Irrational al)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter
          (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * al) ∧ Int.fract ((n : ℝ) * al) < b)).card : ℝ)
          / (N : ℝ))
      atTop (𝓝 (b - a)) := by
  refine equidistribution_of_asymptotic_exists (fun n : ℕ => (n : ℝ) * al)
    (fun h hh => ?_) a b ha hab hb
  simpa using tendsto_exp_average_irrational al hal h hh

end Brockian.Equidistribution

