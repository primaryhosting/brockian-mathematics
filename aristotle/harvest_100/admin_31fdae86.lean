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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic

This file proves **Weyl's criterion**: if a real sequence `x` satisfies the asymptotic
exponential-sum estimate `∑_{n < N} e(h * xₙ) = o(N)` for every nonzero integer `h`, then `x`
is equidistributed modulo one, i.e. for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
indices `n < N` with `Int.fract (xₙ) ∈ [a, b)` tends to `b - a`.
-/

open Filter Finset MeasureTheory Metric Set Submodule
open scoped BigOperators Real Topology

namespace Brockian.Equidistribution

noncomputable section

/-- The image of a real sequence in the circle `ℝ / ℤ`. -/
def pts (x : ℕ → ℝ) (n : ℕ) : AddCircle (1 : ℝ) := ((x n : ℝ) : AddCircle (1 : ℝ))

/-- Weyl's exponential-sum hypothesis for the sequence `x`: for every nonzero integer `h` the
exponential sums `∑_{n < N} e(h xₙ)` are `o(N)`. -/
def WeylSums (x : ℕ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * π * Complex.I * h * x n)) atTop (𝓝 0)

/-- The Cesàro averages of `F` along the orbit converge to the integral of `F`. -/
def AvgTendsto (x : ℕ → ℝ) (F : AddCircle (1 : ℝ) → ℂ) : Prop :=
  Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n)) atTop
    (𝓝 (∫ t : AddCircle (1 : ℝ), F t))

lemma integrable_of_continuous (f : AddCircle (1 : ℝ) → ℂ) (hf : Continuous f) :
    Integrable f volume :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of the Fourier monomial `fourier k` over the circle. -/
lemma integral_fourier_eq (k : ℤ) :
    (∫ t : AddCircle (1 : ℝ), fourier k t) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp only [fourier_zero]
    rw [integral_const, measureReal_def, AddCircle.measure_univ]
    simp
  · exact integral_eq_zero_of_add_right_eq_neg (μ := volume)
      (fourier_add_half_inv_index hk one_pos)

lemma avgTendsto_fourier (x : ℕ → ℝ) (hw : WeylSums x) (k : ℤ) : AvgTendsto x (fourier k) := by
  unfold AvgTendsto
  rw [integral_fourier_eq]
  rcases eq_or_ne k 0 with rfl | hk
  · simp only []
    apply Tendsto.congr' (f₁ := fun _ : ℕ => (1 : ℂ))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      simp [pts, Nat.cast_ne_zero.mpr hN.ne']
    · exact tendsto_const_nhds
  · rw [if_neg hk]
    refine (hw k hk).congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pts, fourier_coe_apply]
    norm_num

lemma avgTendsto_add {x : ℕ → ℝ} {f g : AddCircle (1 : ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hF : AvgTendsto x f) (hG : AvgTendsto x g) :
    AvgTendsto x (fun t => f t + g t) := by
  unfold AvgTendsto at *
  rw [integral_add (integrable_of_continuous _ hf) (integrable_of_continuous _ hg)]
  refine (hF.add hG).congr fun N => ?_
  simp [Finset.sum_add_distrib, mul_add]

lemma avgTendsto_const_mul {x : ℕ → ℝ} {f : AddCircle (1 : ℝ) → ℂ} (c : ℂ)
    (hF : AvgTendsto x f) : AvgTendsto x (fun t => c * f t) := by
  unfold AvgTendsto at *
  rw [integral_const_mul]
  refine (hF.const_mul c).congr fun N => ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma avgTendsto_span (x : ℕ → ℝ) (hw : WeylSums x) (F : C(AddCircle (1 : ℝ), ℂ))
    (hF : F ∈ span ℂ (Set.range (fourier (T := (1 : ℝ))))) : AvgTendsto x F := by
  induction hF using Submodule.span_induction with
  | mem G hG => obtain ⟨k, rfl⟩ := hG; exact avgTendsto_fourier x hw k
  | zero => simp [AvgTendsto]
  | add G H _ _ ihG ihH => exact avgTendsto_add G.continuous H.continuous ihG ihH
  | smul c G _ ihG => exact avgTendsto_const_mul c ihG

/-- Uniform approximation by functions with convergent averages preserves convergence. -/
lemma avgTendsto_of_approx (x : ℕ → ℝ) (F : C(AddCircle (1 : ℝ), ℂ))
    (h : ∀ ε > 0, ∃ G : C(AddCircle (1 : ℝ), ℂ), AvgTendsto x G ∧ ∀ t, ‖F t - G t‖ ≤ ε) :
    AvgTendsto x F := by
  rw [AvgTendsto, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨G, hG, hd⟩ := h (δ / 4) (by linarith)
  rw [AvgTendsto, Metric.tendsto_atTop] at hG
  obtain ⟨N₁, hN₁⟩ := hG (δ / 4) (by linarith)
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have b1 : ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n) - (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n)‖
      ≤ δ / 4 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ n ∈ range N, (F (pts x n) - G (pts x n))‖ ≤ N * (δ / 4) := by
      calc ‖∑ n ∈ range N, (F (pts x n) - G (pts x n))‖
          ≤ ∑ n ∈ range N, ‖F (pts x n) - G (pts x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (δ / 4) := Finset.sum_le_sum fun n _ => hd _
        _ = N * (δ / 4) := by simp
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ range N, (F (pts x n) - G (pts x n))‖
        ≤ (N : ℝ)⁻¹ * (N * (δ / 4)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = δ / 4 := by field_simp
  have b3 : ‖(∫ t : AddCircle (1 : ℝ), G t) - ∫ t : AddCircle (1 : ℝ), F t‖ ≤ δ / 4 := by
    rw [← integral_sub (integrable_of_continuous _ G.continuous)
      (integrable_of_continuous _ F.continuous)]
    have hb : ‖∫ t : AddCircle (1 : ℝ), (G t - F t)‖
        ≤ (δ / 4) * (volume (univ : Set (AddCircle (1 : ℝ)))).toReal := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards with t
      rw [← norm_neg]
      simpa using hd t
    rw [AddCircle.measure_univ] at hb
    simpa using hb
  have b2 := (hN₁ N (le_trans (le_max_left _ _) hN)).le
  rw [Complex.dist_eq] at b2 ⊢
  calc ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n) - ∫ t : AddCircle (1 : ℝ), F t‖
      ≤ ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n) - (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n)‖
        + ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n) - ∫ t : AddCircle (1 : ℝ), G t‖
        + ‖(∫ t : AddCircle (1 : ℝ), G t) - ∫ t : AddCircle (1 : ℝ), F t‖ := by
        have := norm_add₃_le
          (a := (N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n)
            - (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n))
          (b := (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n) - ∫ t : AddCircle (1 : ℝ), G t)
          (c := (∫ t : AddCircle (1 : ℝ), G t) - ∫ t : AddCircle (1 : ℝ), F t)
        simpa using this
    _ ≤ δ / 4 + δ / 4 + δ / 4 := by gcongr
    _ < δ := by linarith

/-- Trigonometric polynomials are uniformly dense in the continuous functions on the circle. -/
lemma exists_trig_approx (F : C(AddCircle (1 : ℝ), ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(AddCircle (1 : ℝ), ℂ), G ∈ span ℂ (Set.range (fourier (T := (1 : ℝ)))) ∧
      ∀ t, ‖F t - G t‖ ≤ ε := by
  have hmem : F ∈ closure
      ((span ℂ (Set.range (fourier (T := (1 : ℝ))))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨G, hGmem, hGd⟩ := hmem ε hε
  refine ⟨G, hGmem, fun t => ?_⟩
  have hFG : ‖F - G‖ ≤ ε := by rw [← dist_eq_norm]; exact hGd.le
  calc ‖F t - G t‖ = ‖(F - G) t‖ := by simp
    _ ≤ ‖F - G‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ε := hFG

lemma avgTendsto_continuous (x : ℕ → ℝ) (hw : WeylSums x) (F : C(AddCircle (1 : ℝ), ℂ)) :
    AvgTendsto x F := by
  refine avgTendsto_of_approx x F fun ε hε => ?_
  obtain ⟨G, hGmem, hGd⟩ := exists_trig_approx F hε
  exact ⟨G, avgTendsto_span x hw G hGmem, hGd⟩

/-- Weyl's criterion, integral form: the Cesàro averages of a continuous real function along the
orbit converge to the integral of the function over the circle. -/
lemma tendsto_avg_real (x : ℕ → ℝ) (hw : WeylSums x) (f : AddCircle (1 : ℝ) → ℝ)
    (hf : Continuous f) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, f (pts x n)) atTop
      (𝓝 (∫ t : AddCircle (1 : ℝ), f t)) := by
  have h := avgTendsto_continuous x hw ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp hf⟩
  rw [AvgTendsto] at h
  simp only [ContinuousMap.coe_mk, integral_complex_ofReal] at h
  refine ((Complex.continuous_re.tendsto _).comp h).congr fun N => ?_
  simp [Function.comp, ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul]

/-! ### Continuous approximations to the indicator of an arc -/

/-- Continuous upper approximation to the indicator function of the closed arc of radius `r`
centred at `c`; it equals `1` on that arc and vanishes outside the arc of radius `r + ε`. -/
def arcUpper (c : AddCircle (1 : ℝ)) (r ε : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  fun t => min 1 (max 0 ((r + ε - dist t c) / ε))

/-- Continuous lower approximation to the indicator function of the closed arc of radius `r`
centred at `c`; it equals `1` on the arc of radius `r - ε` and vanishes outside the arc of
radius `r`. -/
def arcLower (c : AddCircle (1 : ℝ)) (r ε : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  fun t => min 1 (max 0 ((r - dist t c) / ε))

lemma continuous_arcUpper (c : AddCircle (1 : ℝ)) (r ε : ℝ) : Continuous (arcUpper c r ε) := by
  unfold arcUpper; fun_prop

lemma continuous_arcLower (c : AddCircle (1 : ℝ)) (r ε : ℝ) : Continuous (arcLower c r ε) := by
  unfold arcLower; fun_prop

lemma arcUpper_nonneg (c : AddCircle (1 : ℝ)) (r ε : ℝ) (t : AddCircle (1 : ℝ)) :
    0 ≤ arcUpper c r ε t :=
  le_min zero_le_one (le_max_left _ _)

lemma arcLower_le_one (c : AddCircle (1 : ℝ)) (r ε : ℝ) (t : AddCircle (1 : ℝ)) :
    arcLower c r ε t ≤ 1 :=
  min_le_left _ _

lemma integral_arcUpper_le (c : AddCircle (1 : ℝ)) (r ε : ℝ) (hε : 0 < ε) (hr : 0 ≤ r) :
    (∫ t : AddCircle (1 : ℝ), arcUpper c r ε t) ≤ 2 * r + 2 * ε := by
  have hle : ∀ t, arcUpper c r ε t ≤ (closedBall c (r + ε)).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ closedBall c (r + ε)
    · rw [indicator_of_mem ht]; exact min_le_left _ _
    · rw [indicator_of_notMem ht]
      simp only [mem_closedBall, not_le] at ht
      have hz : (r + ε - dist t c) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
      simp [arcUpper, max_eq_left hz]
  have hint : (∫ t : AddCircle (1 : ℝ), arcUpper c r ε t)
      ≤ ∫ t : AddCircle (1 : ℝ), (closedBall c (r + ε)).indicator (fun _ => (1 : ℝ)) t :=
    integral_mono ((continuous_arcUpper c r ε).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall) hle
  refine hint.trans ?_
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, smul_eq_mul, mul_one,
    measureReal_def, AddCircle.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  exact (min_le_right _ _).trans (by linarith)

lemma le_integral_arcLower (c : AddCircle (1 : ℝ)) (r ε : ℝ) (hε : 0 < ε) (hr : 2 * (r - ε) ≤ 1) :
    2 * r - 2 * ε ≤ ∫ t : AddCircle (1 : ℝ), arcLower c r ε t := by
  have hle : ∀ t, (closedBall c (r - ε)).indicator (fun _ => (1 : ℝ)) t ≤ arcLower c r ε t := by
    intro t
    by_cases ht : t ∈ closedBall c (r - ε)
    · rw [indicator_of_mem ht]
      simp only [mem_closedBall] at ht
      refine le_min le_rfl (le_max_of_le_right ?_)
      rw [le_div_iff₀ hε]
      linarith
    · rw [indicator_of_notMem ht]
      exact le_min zero_le_one (le_max_left _ _)
  have hint : (∫ t : AddCircle (1 : ℝ), (closedBall c (r - ε)).indicator (fun _ => (1 : ℝ)) t)
      ≤ ∫ t : AddCircle (1 : ℝ), arcLower c r ε t :=
    integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      ((continuous_arcLower c r ε).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) hle
  refine le_trans ?_ hint
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, smul_eq_mul, mul_one,
    measureReal_def, AddCircle.volume_closedBall]
  rcases le_or_gt 0 (2 * (r - ε)) with h | h
  · rw [ENNReal.toReal_ofReal (le_min (by norm_num) h), le_min_iff]
    constructor <;> linarith
  · have hzero : ENNReal.ofReal (min (1 : ℝ) (2 * (r - ε))) = 0 := by
      rw [ENNReal.ofReal_eq_zero]
      exact (min_le_right _ _).trans h.le
    rw [hzero]
    simp only [ENNReal.toReal_zero]
    linarith

/-! ### The arc geometry of `[a, b) ⊆ [0, 1)` -/

lemma dist_coe_le_of_mem_Ico {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hy : y ∈ Set.Ico a b) :
    dist ((y : AddCircle (1 : ℝ))) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ≤ (b - a) / 2 := by
  obtain ⟨hy1, hy2⟩ := hy
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  have hr : round (y - (a + b) / 2) = 0 := by
    rw [round_eq_zero_iff]
    constructor <;> simp <;> linarith
  rw [hr]
  simp only [Int.cast_zero, sub_zero, abs_le]
  constructor <;> linarith

lemma mem_Ico_of_dist_coe_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hd : dist ((y : AddCircle (1 : ℝ))) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) < (b - a) / 2) :
    y ∈ Set.Ico a b := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq] at hd
  set k : ℤ := round (y - (a + b) / 2) with hk
  rw [abs_lt] at hd
  obtain ⟨h1, h2⟩ := hd
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith
    · have hge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
      linarith
  rw [hk0] at h1 h2
  simp only [Int.cast_zero, sub_zero] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Weyl's criterion.**  If the exponential sums `∑_{n < N} e(h xₙ)` are `o(N)` for every
nonzero integer `h`, then the sequence `x` is equidistributed modulo one. -/
theorem equidistribution_of_asymptotic (x : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
        Complex.exp (2 * π * Complex.I * h * x n)) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  have hW : WeylSums x := hw
  set c : AddCircle (1 : ℝ) := (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) with hc
  set r : ℝ := (b - a) / 2 with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hr1 : 2 * r ≤ 1 := by rw [hrdef]; linarith
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := δ / 8 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hU := tendsto_avg_real x hW (arcUpper c r ε) (continuous_arcUpper c r ε)
  have hL := tendsto_avg_real x hW (arcLower c r ε) (continuous_arcLower c r ε)
  rw [Metric.tendsto_atTop] at hU hL
  obtain ⟨N₁, hN₁⟩ := hU (δ / 8) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hL (δ / 8) (by linarith)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hIU : (∫ t : AddCircle (1 : ℝ), arcUpper c r ε t) ≤ 2 * r + 2 * ε :=
    integral_arcUpper_le c r ε hε hr0
  have hIL : 2 * r - 2 * ε ≤ ∫ t : AddCircle (1 : ℝ), arcLower c r ε t :=
    le_integral_arcLower c r ε hε (by linarith)
  -- the pointwise sandwich of the indicator between the two continuous functions
  have key : ∀ n : ℕ,
      arcLower c r ε (pts x n) ≤ (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) ∧
        (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) ≤ arcUpper c r ε (pts x n) := by
    intro n
    have hpt : pts x n = ((Int.fract (x n) : ℝ) : AddCircle (1 : ℝ)) := by
      rw [pts, AddCircle.coe_fract]
    by_cases hmem : Int.fract (x n) ∈ Set.Ico a b
    · refine ⟨by rw [if_pos hmem]; exact arcLower_le_one c r ε _, ?_⟩
      rw [if_pos hmem]
      have hd : dist (pts x n) c ≤ r := by
        rw [hpt, hc, hrdef]; exact dist_coe_le_of_mem_Ico ha hb hmem
      refine le_min le_rfl (le_max_of_le_right ?_)
      rw [le_div_iff₀ hε]
      linarith
    · refine ⟨?_, by rw [if_neg hmem]; exact arcUpper_nonneg c r ε _⟩
      rw [if_neg hmem]
      have hd : r ≤ dist (pts x n) c := by
        by_contra hlt
        push_neg at hlt
        refine hmem (mem_Ico_of_dist_coe_lt ha hb (Int.fract_nonneg _) (Int.fract_lt_one _) ?_)
        rw [← hc, ← hrdef, ← hpt]
        exact hlt
      have hz : (r - dist (pts x n) c) / ε ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
      simp [arcLower, max_eq_left hz]
  have hcard : (((range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ)
      = ∑ n ∈ range N, (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) :=
    (Finset.sum_boole _ _).symm
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hlow : (N : ℝ)⁻¹ * ∑ n ∈ range N, arcLower c r ε (pts x n)
      ≤ (((range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ) / N := by
    rw [div_eq_inv_mul, hcard]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => (key n).1) hNinv
  have hhigh : (((range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ) / N
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, arcUpper c r ε (pts x n) := by
    rw [div_eq_inv_mul, hcard]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => (key n).2) hNinv
  have hu := hN₁ N (le_trans (le_max_left _ _) hN)
  have hl := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hu hl
  rw [Real.dist_eq, abs_lt]
  have hba : 2 * r = b - a := by rw [hrdef]; ring
  constructor <;> [linarith [hu.1, hl.1]; linarith [hu.2, hl.2]]

end

end Brockian.Equidistribution

