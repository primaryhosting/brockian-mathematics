import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/
def cavg (x : ℕ → ℝ) (f : 𝕋 → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)

lemma cavg_add (x : ℕ → ℝ) (f g : 𝕋 → ℂ) (N : ℕ) :
    cavg x (f + g) N = cavg x f N + cavg x g N := by
  simp [cavg, Finset.sum_add_distrib, mul_add]

lemma cavg_sub (x : ℕ → ℝ) (f g : 𝕋 → ℂ) (N : ℕ) :
    cavg x (f - g) N = cavg x f N - cavg x g N := by
  simp [cavg, Finset.sum_sub_distrib, mul_sub]

lemma cavg_smul (x : ℕ → ℝ) (c : ℂ) (f : 𝕋 → ℂ) (N : ℕ) :
    cavg x (c • f) N = c * cavg x f N := by
  simp only [cavg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma integrable_cm (f : C(𝕋, ℂ)) : Integrable f (volume : Measure 𝕋) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma norm_cavg_le (x : ℕ → ℝ) (f : C(𝕋, ℂ)) (N : ℕ) : ‖cavg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cavg, norm_nonneg]
  · rw [cavg, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)‖
          ≤ ∑ n ∈ Finset.range N, ‖f ((x n : ℝ) : 𝕋)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum (fun _ _ => f.norm_coe_le_norm _)
        _ = N * ‖f‖ := by simp
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    rw [inv_mul_le_iff₀ hNpos]
    exact h1

lemma norm_integral_le_norm (f : C(𝕋, ℂ)) : ‖∫ z, f z‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure 𝕋)) (C := ‖f‖)
    (f := fun z => f z) (Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm z))
  have hu : (volume : Measure 𝕋).real Set.univ = 1 := by
    simp [measureReal_def, AddCircle.measure_univ]
  rwa [hu, mul_one] at h

/-- The continuous test functions along which the sequence `x` equidistributes, as a
`ℂ`-submodule of `C(ℝ/ℤ, ℂ)`. -/
def Equidist (x : ℕ → ℝ) : Submodule ℂ C(𝕋, ℂ) where
  carrier := {f | Tendsto (cavg x f) atTop (𝓝 (∫ z, f z))}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    have h1 : (∫ z, (f + g) z) = (∫ z, f z) + ∫ z, g z := by
      simp only [ContinuousMap.coe_add, Pi.add_apply]
      exact integral_add (integrable_cm f) (integrable_cm g)
    rw [h1]
    refine (hf.add hg).congr (fun N => ?_)
    simp [cavg, Finset.sum_add_distrib, mul_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have h : cavg x ⇑(0 : C(𝕋, ℂ)) = fun _ => (0 : ℂ) := by funext N; simp [cavg]
    rw [h]
    simp
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    have h1 : (∫ z, (c • f) z) = c * ∫ z, f z := by
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [MeasureTheory.integral_const_mul]
    rw [h1]
    refine (hf.const_mul c).congr (fun N => ?_)
    rw [ContinuousMap.coe_smul, cavg_smul]

lemma mem_equidist_iff {x : ℕ → ℝ} {f : C(𝕋, ℂ)} :
    f ∈ Equidist x ↔ Tendsto (cavg x f) atTop (𝓝 (∫ z, f z)) := Iff.rfl

lemma isClosed_equidist (x : ℕ → ℝ) : IsClosed (Equidist x : Set C(𝕋, ℂ)) := by
  apply isClosed_of_closure_subset
  intro f hf
  show Tendsto (cavg x f) atTop (𝓝 (∫ z, f z))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by positivity)
  rw [SetLike.mem_coe, mem_equidist_iff] at hg
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hg (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have e1 : ‖cavg x f N - cavg x g N‖ ≤ ‖f - g‖ := by
    rw [← cavg_sub]
    simpa [ContinuousMap.coe_sub] using norm_cavg_le x (f - g) N
  have e3 : ‖(∫ z, g z) - ∫ z, f z‖ ≤ ‖f - g‖ := by
    rw [← integral_sub (integrable_cm g) (integrable_cm f)]
    have h := norm_integral_le_norm (g - f)
    simp only [ContinuousMap.coe_sub, Pi.sub_apply] at h
    rw [show ‖f - g‖ = ‖g - f‖ from norm_sub_rev f g]
    exact h
  have hd : ‖f - g‖ < ε / 3 := by rw [← dist_eq_norm]; exact hfg
  calc dist (cavg x f N) (∫ z, f z)
      ≤ dist (cavg x f N) (cavg x g N) + dist (cavg x g N) (∫ z, g z)
        + dist (∫ z, g z) (∫ z, f z) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · rw [dist_eq_norm]; exact lt_of_le_of_lt e1 hd
        · exact hN₀ N hN
        · rw [dist_eq_norm]; exact lt_of_le_of_lt e3 hd
    _ = ε := by ring

/-- The integral of a Fourier monomial over the circle. -/
lemma integral_fourier (h : ℤ) : (∫ z : 𝕋, fourier h z) = if h = 0 then 1 else 0 := by
  have hv : (volume : Measure 𝕋) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have h0 := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) h) 0
  rw [fourierCoeff] at h0
  simp only [neg_zero, fourier_zero, one_smul] at h0
  rw [hv, h0]
  by_cases hh : h = 0 <;> simp [hh, Pi.single_apply, eq_comm]

/-- Weyl's criterion: vanishing of all nontrivial exponential sums forces convergence of the
Cesàro averages of every continuous test function to its mean. -/
lemma equidist_eq_top (x : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 → Tendsto (cavg x (fourier h)) atTop (𝓝 0)) :
    Equidist x = ⊤ := by
  have hfour : ∀ h : ℤ, (fourier h : C(𝕋, ℂ)) ∈ Equidist x := by
    intro h
    rw [mem_equidist_iff, integral_fourier]
    by_cases hh : h = 0
    · subst hh
      have hev : ∀ N : ℕ, 1 ≤ N → cavg x (fourier (0 : ℤ)) N = 1 := by
        intro N hN
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp [cavg, hN0]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop))
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hev N hN).symm
    · simpa [hh] using hw h hh
  have hspan : Submodule.span ℂ (Set.range (fourier : ℤ → C(𝕋, ℂ))) ≤ Equidist x :=
    Submodule.span_le.mpr (by rintro f ⟨h, rfl⟩; exact hfour h)
  have hcl := Submodule.topologicalClosure_mono hspan
  rw [span_fourier_closure_eq_top] at hcl
  have hc : (Equidist x).topologicalClosure = Equidist x :=
    SetLike.ext' (isClosed_equidist x).closure_eq
  rw [hc] at hcl
  exact top_le_iff.mp hcl

/-- Weyl's criterion for real-valued continuous test functions. -/
lemma tendsto_cavg_real (x : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 → Tendsto (cavg x (fourier h)) atTop (𝓝 0)) (f : C(𝕋, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)) atTop
      (𝓝 (∫ z, f z)) := by
  set F : C(𝕋, ℂ) := ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hmem : F ∈ Equidist x := by rw [equidist_eq_top x hw]; trivial
  rw [mem_equidist_iff] at hmem
  have hint : (∫ z, F z) = ((∫ z, f z : ℝ) : ℂ) := integral_complex_ofReal
  rw [hint] at hmem
  have hre := (Complex.continuous_re.tendsto _).comp hmem
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  refine hre.congr (fun N => ?_)
  have hc : cavg x F N = (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋) : ℝ) : ℂ) := by
    simp [cavg, hF]
  rw [hc, Complex.ofReal_re]

lemma integrable_cmR (f : C(𝕋, ℝ)) : Integrable f (volume : Measure 𝕋) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Geometry of the circle -/

/-- The circle norm is bounded by the distance to any integer translate. -/
lemma norm_coe_le_abs_sub_int (z : ℝ) (k : ℤ) : ‖((z : ℝ) : 𝕋)‖ ≤ |z - k| := by
  rw [AddCircle.norm_eq]
  simpa using round_le z k

lemma exists_int_of_norm_lt {z r : ℝ} (h : ‖((z : ℝ) : 𝕋)‖ < r) : ∃ k : ℤ, |z - k| < r := by
  refine ⟨round z, ?_⟩
  rw [AddCircle.norm_eq] at h
  simpa using h

lemma dist_coe_eq (y m : ℝ) : dist ((y : ℝ) : 𝕋) ((m : ℝ) : 𝕋) = ‖((y - m : ℝ) : 𝕋)‖ := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]

/-- If the fractional part of `y` lies in `[a, b)` then, on the circle, `y` is within `(b-a)/2`
of the midpoint of the arc. -/
lemma dist_le_of_fract_mem {a b y : ℝ} (h : Int.fract y ∈ Set.Ico a b) :
    dist ((y : ℝ) : 𝕋) (((a + b) / 2 : ℝ) : 𝕋) ≤ (b - a) / 2 := by
  rw [dist_coe_eq]
  refine le_trans (norm_coe_le_abs_sub_int _ ⌊y⌋) ?_
  have hy : y - (a + b) / 2 - ⌊y⌋ = Int.fract y - (a + b) / 2 := by
    rw [← Int.self_sub_floor y]; ring
  rw [hy, abs_le]
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

/-- Conversely, points of the open arc have fractional part in `[a, b)`. -/
lemma fract_mem_of_dist_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (h : dist ((y : ℝ) : 𝕋) (((a + b) / 2 : ℝ) : 𝕋) < (b - a) / 2) :
    Int.fract y ∈ Set.Ico a b := by
  rw [dist_coe_eq] at h
  obtain ⟨k, hk⟩ := exists_int_of_norm_lt h
  rw [abs_lt] at hk
  have h1 : a < y - k := by linarith [hk.1]
  have h2 : y - k < b := by linarith [hk.2]
  have hfr : Int.fract y = y - k := by
    have hs : Int.fract (y - k) = y - k := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [← hs, Int.fract_sub_intCast]
  rw [hfr]
  exact ⟨le_of_lt h1, h2⟩

/-! ### Continuous approximations of arc indicators -/

/-- A continuous "plateau" function on the circle: it equals `1` on `closedBall c s` and
vanishes outside `closedBall c (s + ε)`. -/
def plateau (c : 𝕋) (s ε : ℝ) : C(𝕋, ℝ) :=
  ⟨fun z => min 1 (max 0 ((s + ε - dist z c) / ε)), by
    apply Continuous.min continuous_const
    apply Continuous.max continuous_const
    exact (continuous_const.sub (continuous_id.dist continuous_const)).div_const ε⟩

lemma plateau_nonneg (c : 𝕋) (s ε : ℝ) (z : 𝕋) : 0 ≤ plateau c s ε z := by
  simp only [plateau, ContinuousMap.coe_mk, le_min_iff]
  exact ⟨zero_le_one, le_max_left _ _⟩

lemma plateau_le_one (c : 𝕋) (s ε : ℝ) (z : 𝕋) : plateau c s ε z ≤ 1 := min_le_left _ _

lemma plateau_eq_one {c : 𝕋} {s ε : ℝ} (hε : 0 < ε) {z : 𝕋} (hz : dist z c ≤ s) :
    plateau c s ε z = 1 := by
  simp only [plateau, ContinuousMap.coe_mk]
  have h : (1 : ℝ) ≤ (s + ε - dist z c) / ε := by rw [le_div_iff₀ hε]; linarith
  exact min_eq_left (le_max_of_le_right h)

lemma plateau_eq_zero {c : 𝕋} {s ε : ℝ} (hε : 0 < ε) {z : 𝕋} (hz : s + ε ≤ dist z c) :
    plateau c s ε z = 0 := by
  simp only [plateau, ContinuousMap.coe_mk]
  have h : (s + ε - dist z c) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [max_eq_left h, min_eq_right zero_le_one]

lemma integral_plateau_le (c : 𝕋) (s ε : ℝ) (hε : 0 < ε) (hs : 0 ≤ s + ε) :
    (∫ z, plateau c s ε z) ≤ 2 * (s + ε) := by
  have hind : Integrable ((closedBall c (s + ε)).indicator (fun _ => (1 : ℝ)))
      (volume : Measure 𝕋) := (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  have hle : ∀ z, plateau c s ε z ≤ (closedBall c (s + ε)).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ closedBall c (s + ε)
    · rw [Set.indicator_of_mem hz]; exact plateau_le_one _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      rw [mem_closedBall, not_le] at hz
      exact le_of_eq (plateau_eq_zero hε hz.le)
  calc (∫ z, plateau c s ε z)
      ≤ ∫ z, (closedBall c (s + ε)).indicator (fun _ => (1 : ℝ)) z :=
        integral_mono (integrable_cmR _) hind hle
    _ = (volume : Measure 𝕋).real (closedBall c (s + ε)) := by
        rw [integral_indicator_const _ measurableSet_closedBall]; simp
    _ ≤ 2 * (s + ε) := by
        rw [measureReal_def, AddCircle.volume_closedBall]
        rcases le_total 1 (2 * (s + ε)) with h1 | h1
        · rw [min_eq_left h1, ENNReal.toReal_ofReal zero_le_one]; linarith
        · rw [min_eq_right h1, ENNReal.toReal_ofReal (by linarith)]

lemma le_integral_plateau (c : 𝕋) (s ε : ℝ) (hε : 0 < ε) (hs : 0 ≤ s) (h1 : 2 * s ≤ 1) :
    2 * s ≤ ∫ z, plateau c s ε z := by
  have hind : Integrable ((closedBall c s).indicator (fun _ => (1 : ℝ)))
      (volume : Measure 𝕋) := (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  have hle : ∀ z, (closedBall c s).indicator (fun _ => (1 : ℝ)) z ≤ plateau c s ε z := by
    intro z
    by_cases hz : z ∈ closedBall c s
    · rw [Set.indicator_of_mem hz, plateau_eq_one hε (mem_closedBall.mp hz)]
    · rw [Set.indicator_of_notMem hz]; exact plateau_nonneg _ _ _ _
  calc 2 * s = (volume : Measure 𝕋).real (closedBall c s) := by
        rw [measureReal_def, AddCircle.volume_closedBall, min_eq_right h1,
          ENNReal.toReal_ofReal (by linarith)]
    _ = ∫ z, (closedBall c s).indicator (fun _ => (1 : ℝ)) z := by
        rw [integral_indicator_const _ measurableSet_closedBall]; simp
    _ ≤ ∫ z, plateau c s ε z := integral_mono hind (integrable_cmR _) hle

/-! ### Counting and the main theorem -/

/-- The number of indices `n < N` whose fractional part lands in `[a, b)`. -/
def arcCount (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card

lemma arcCount_cast (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (arcCount x a b N : ℝ)
      = ∑ n ∈ Finset.range N, if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0 := by
  rw [arcCount, Finset.card_filter]
  push_cast
  rfl

lemma arcCount_le_sum (x : ℕ → ℝ) {a b ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (arcCount x a b N : ℝ)
      ≤ ∑ n ∈ Finset.range N,
          plateau (((a + b) / 2 : ℝ) : 𝕋) ((b - a) / 2) ε ((x n : ℝ) : 𝕋) := by
  rw [arcCount_cast]
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hn : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hn, plateau_eq_one hε (dist_le_of_fract_mem hn)]
  · rw [if_neg hn]; exact plateau_nonneg _ _ _ _

lemma sum_le_arcCount (x : ℕ → ℝ) {a b ε : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : b ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        plateau (((a + b) / 2 : ℝ) : 𝕋) ((b - a) / 2 - ε) ε ((x n : ℝ) : 𝕋)
      ≤ (arcCount x a b N : ℝ) := by
  rw [arcCount_cast]
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hn : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hn]; exact plateau_le_one _ _ _ _
  · rw [if_neg hn]
    refine le_of_eq (plateau_eq_zero hε ?_)
    have : ¬ dist ((x n : ℝ) : 𝕋) (((a + b) / 2 : ℝ) : 𝕋) < (b - a) / 2 := fun hlt =>
      hn (fract_mem_of_dist_lt ha hb hlt)
    push_neg at this
    linarith

/-- **Weyl's equidistribution theorem.** If all nontrivial exponential sums of a real sequence
`x` have vanishing Cesàro averages, then the sequence is equidistributed modulo one: for every
subinterval `[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies
in `[a, b)` tends to `b - a`. -/
theorem equidistribution_of_asymptotic (x : ℕ → ℝ)
    (hweyl : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * h * x n)) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        ((((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ)) / N)
      atTop (𝓝 (b - a)) := by
  have hw : ∀ h : ℤ, h ≠ 0 → Tendsto (cavg x (fourier h)) atTop (𝓝 0) := by
    intro h hh
    refine (hweyl h hh).congr (fun N => ?_)
    simp only [cavg, fourier_coe_apply]
    norm_num
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := δ / 4 with hεdef
  have hε : 0 < ε := by positivity
  set c : 𝕋 := (((a + b) / 2 : ℝ) : 𝕋) with hc
  set r : ℝ := (b - a) / 2 with hr
  set U : C(𝕋, ℝ) := plateau c r ε with hU
  set L : C(𝕋, ℝ) := plateau c (r - ε) ε with hL
  have hIU : (∫ z, U z) ≤ (b - a) + 2 * ε := by
    have := integral_plateau_le c r ε hε (by simp only [hr]; linarith)
    simp only [hU]
    linarith [this]
  have hIL : (b - a) - 2 * ε ≤ ∫ z, L z := by
    rcases le_or_gt 0 (r - ε) with hpos | hneg
    · have h2 : 2 * (r - ε) ≤ 1 := by simp only [hr]; linarith
      have := le_integral_plateau c (r - ε) ε hε hpos h2
      simp only [hL]
      linarith [this]
    · have hnn : (0 : ℝ) ≤ ∫ z, L z :=
        integral_nonneg (fun z => plateau_nonneg _ _ _ _)
      simp only [hr] at hneg
      linarith
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tendsto_cavg_real x hw U) ε hε
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp (tendsto_cavg_real x hw L) ε hε
  refine ⟨max 1 (max N₁ N₂), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hup := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN)
  have hlo := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at hup hlo ⊢
  have hcU : (arcCount x a b N : ℝ) / N
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, U ((x n : ℝ) : 𝕋) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (arcCount_le_sum x hε N) (by positivity)
  have hcL : (N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, L ((x n : ℝ) : 𝕋))
      ≤ (arcCount x a b N : ℝ) / N := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (sum_le_arcCount x hε ha hb N) (by positivity)
  have hgoal : (arcCount x a b N : ℝ) / N
      = ((((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ)) / N := rfl
  rw [← hgoal]
  constructor
  · have : (b - a) - 3 * ε < (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, L ((x n : ℝ) : 𝕋) := by
      linarith [hlo.1, hIL]
    have h4 : 3 * ε < δ := by rw [hεdef]; linarith
    linarith [hcL]
  · have : (N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, U ((x n : ℝ) : 𝕋)) < (b - a) + 3 * ε := by
      linarith [hup.2, hIU]
    have h4 : 3 * ε < δ := by rw [hεdef]; linarith
    linarith [hcU]

/-! ### An instance of the hypothesis: irrational rotations -/

/-- The Weyl sums of the sequence `n ↦ n * α` vanish in the Cesàro sense whenever `α` is
irrational. -/
lemma weyl_sums_tendsto_zero_of_irrational {α : ℝ} (hα : Irrational α) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ))) atTop (𝓝 0) := by
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * h * α) with hwdef
  have hwn : ‖w‖ = 1 := by rw [hwdef, Complex.norm_exp]; norm_num
  have hw1 : w ≠ 1 := by
    intro hcon
    rw [hwdef, Complex.exp_eq_one_iff] at hcon
    obtain ⟨k, hk⟩ := hcon
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h3 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have h2 : (2 : ℂ) * Real.pi * Complex.I * ((h : ℂ) * α)
        = (2 : ℂ) * Real.pi * Complex.I * k := by
      rw [show (2 : ℂ) * Real.pi * Complex.I * ((h : ℂ) * α)
            = 2 * Real.pi * Complex.I * h * α by ring, hk]
      ring
    have hc : (h : ℂ) * α = k := mul_left_cancel₀ h3 h2
    have hreal : (h : ℝ) * α = k := by exact_mod_cast hc
    have hirr : Irrational ((h : ℝ) * α) := hα.intCast_mul hh
    rw [hreal] at hirr
    exact (Rat.not_irrational k) (by exact_mod_cast hirr)
  have hterm : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ)) = w ^ n := by
    intro n
    rw [hwdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hd : 0 < ‖w - 1‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hw1
  have hbound : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ))‖
      ≤ (2 / ‖w - 1‖) * (N : ℝ)⁻¹ := by
    intro N
    simp only [hterm]
    rw [geom_sum_eq hw1, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have hnum : ‖w ^ N - 1‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_pow, hwn]
      norm_num
    rw [mul_comm ((2 : ℝ) / ‖w - 1‖) ((N : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hd).mpr hnum) (by positivity)
  refine squeeze_zero_norm hbound ?_
  simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 / ‖w - 1‖)

/-- **Weyl's theorem on irrational rotations**, an unconditional consequence of
`equidistribution_of_asymptotic`: for irrational `α`, the sequence `n * α` is equidistributed
modulo one. In particular the hypothesis of `equidistribution_of_asymptotic` is satisfiable. -/
theorem equidistribution_nat_mul_irrational {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        ((((Finset.range N).filter
          (fun n : ℕ => Int.fract ((n : ℝ) * α) ∈ Set.Ico a b)).card : ℝ)) / N)
      atTop (𝓝 (b - a)) :=
  equidistribution_of_asymptotic (fun n => (n : ℝ) * α)
    (fun h hh => weyl_sums_tendsto_zero_of_irrational hα h hh) ha hab hb

end

end Brockian.Equidistribution

