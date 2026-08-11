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
# Equidistribution of irrational rotations and the BV reduction of configuration counts

This file proves, unconditionally, that for an irrational `α` the number of `n < N` with
`Int.fract (n * α)` in a window `[a, b) ⊆ [0, 1]` is asymptotic to the main term `(b - a) * N`.

The equidistribution input (Weyl's theorem for the sequence `n ↦ n α mod 1`) is proved here from
scratch, via Weyl's criterion: the set of continuous test functions on the circle for which the
Birkhoff averages converge to the mean is a closed submodule containing all characters, hence is
everything, by density of trigonometric polynomials.  A bounded-variation ("BV") style sandwich by
continuous trapezoidal functions then transfers the statement to indicator functions of windows.
-/

open MeasureTheory Filter Set Metric Topology Complex
open scoped BigOperators

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- The number of `n < N` for which the fractional part of `n * α` lies in the window `[a, b)`. -/
def configCount (alpha a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * alpha) ∈ Set.Ico a b).card

/-- The expected main term for `configCount`: the window length times the number of samples. -/
def mainTerm (a b : ℝ) (N : ℕ) : ℝ := (b - a) * N

/-- The `N`-th Birkhoff average of a function on the circle along the orbit of `0` under the
rotation by `α`. -/
def circleAvg (alpha : ℝ) (F : AddCircle (1 : ℝ) → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, F ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N

section Weyl

variable (alpha : ℝ)

/-- Continuous functions on the circle are integrable for the (finite) Haar measure. -/
theorem integrable_continuousMap (F : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable (fun y => F y) volume :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Continuous real functions on the circle are integrable for the (finite) Haar measure. -/
theorem integrable_continuousMap_real (f : C(AddCircle (1 : ℝ), ℝ)) :
    Integrable (fun y => f y) volume :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The set of continuous test functions whose Birkhoff averages along the rotation orbit converge
to the mean value, as a submodule of `C(AddCircle 1, ℂ)`. -/
def weylGood : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) where
  carrier := {F | Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y))}
  add_mem' := by
    intro F G hF hG
    simp only [Set.mem_setOf_eq] at hF hG ⊢
    have hsum : ∀ N : ℕ, circleAvg alpha (F + G) N = circleAvg alpha F N + circleAvg alpha G N := by
      intro N; simp [circleAvg, Finset.sum_add_distrib, add_div]
    have hint : (∫ y, (F + G) y) = (∫ y, F y) + ∫ y, G y := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (integrable_continuousMap F) (integrable_continuousMap G)
    rw [hint]
    exact (hF.add hG).congr fun N => (hsum N).symm
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hsum : ∀ N : ℕ, circleAvg alpha (0 : C(AddCircle (1 : ℝ), ℂ)) N = 0 := by
      intro N; simp [circleAvg]
    simp only [ContinuousMap.zero_apply, integral_zero]
    exact tendsto_const_nhds.congr fun N => (hsum N).symm
  smul_mem' := by
    intro c F hF
    simp only [Set.mem_setOf_eq] at hF ⊢
    have hsum : ∀ N : ℕ, circleAvg alpha (c • F) N = c * circleAvg alpha F N := by
      intro N
      simp only [circleAvg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]
    have hint : (∫ y, (c • F) y) = c * ∫ y, F y := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    rw [hint]
    exact (hF.const_mul c).congr fun N => (hsum N).symm

/-- The mean value of a nontrivial character on the circle vanishes. -/
theorem integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ y : AddCircle (1 : ℝ), (fourier k) y) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  rw [fourierCoeff, AddCircle.integral_haarAddCircle] at h
  simp only [Pi.single_apply, if_neg (Ne.symm hk)] at h
  simpa using h

/-- The mean value of the trivial character is `1`. -/
theorem integral_fourier_zero : (∫ y : AddCircle (1 : ℝ), (fourier 0) y) = 1 := by
  simp [AddCircle.measure_univ, measureReal_def]

theorem fourier_mem_weylGood (halpha : Irrational alpha) (k : ℤ) :
    (fourier k : C(AddCircle (1 : ℝ), ℂ)) ∈ weylGood alpha := by
  show Tendsto (circleAvg alpha (fourier k)) atTop (𝓝 _)
  rcases eq_or_ne k 0 with rfl | hk
  · rw [integral_fourier_zero]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp [circleAvg, div_self hN']
  · rw [integral_fourier_eq_zero hk]
    set z : ℂ := (fourier k) ((alpha : ℝ) : AddCircle (1 : ℝ)) with hzdef
    have hz1 : z ≠ 1 := by
      rw [hzdef, fourier_coe_apply]
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have hpi : (2 : ℂ) * Real.pi * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      field_simp at hn
      have hR : (k : ℝ) * alpha = (n : ℝ) := by
        exact_mod_cast (by simpa using hn : (k : ℂ) * alpha = n)
      have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      refine halpha ⟨(n : ℚ) / (k : ℚ), ?_⟩
      push_cast
      field_simp
      linarith [hR]
    have hznorm : ‖z‖ = 1 := by
      rw [hzdef, fourier_coe_apply, Complex.norm_exp]
      norm_num
    have hterm : ∀ n : ℕ, (fourier k) ((n * alpha : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
      intro n
      rw [hzdef, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have hd : 0 < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
    have hbound : ∀ N : ℕ, ‖circleAvg alpha (fourier k) N‖ ≤ (2 / ‖z - 1‖) / N := by
      intro N
      have hsum : ∑ n ∈ Finset.range N, (fourier k) ((n * alpha : ℝ) : AddCircle (1 : ℝ))
          = (z ^ N - 1) / (z - 1) := by
        simp only [hterm]
        exact geom_sum_eq hz1 N
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp [circleAvg]
      · rw [circleAvg, hsum, norm_div, norm_div]
        have h1 : ‖z ^ N - 1‖ ≤ 2 := by
          calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hznorm]; norm_num
        have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
        rw [hcast]
        gcongr
    exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- Birkhoff averages are `1`-Lipschitz in the sup norm of the test function. -/
theorem dist_circleAvg_le (F G : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    dist (circleAvg alpha F N) (circleAvg alpha G N) ≤ dist F G := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [circleAvg, dist_nonneg]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dist_eq_norm, circleAvg, circleAvg, div_sub_div_same, ← Finset.sum_sub_distrib, norm_div]
  have h1 : ‖∑ n ∈ Finset.range N, (F ((n * alpha : ℝ) : AddCircle (1 : ℝ))
      - G ((n * alpha : ℝ) : AddCircle (1 : ℝ)))‖ ≤ N * dist F G := by
    calc ‖∑ n ∈ Finset.range N, (F ((n * alpha : ℝ) : AddCircle (1 : ℝ))
            - G ((n * alpha : ℝ) : AddCircle (1 : ℝ)))‖
        ≤ ∑ n ∈ Finset.range N, ‖F ((n * alpha : ℝ) : AddCircle (1 : ℝ))
            - G ((n * alpha : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, dist F G := by
          refine Finset.sum_le_sum fun n _ => ?_
          simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist
            (f := F) (g := G) ((n * alpha : ℝ) : AddCircle (1 : ℝ))
      _ = N * dist F G := by simp
  have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hcast, div_le_iff₀ hNpos]
  linarith [h1]

/-- Mean values are `1`-Lipschitz in the sup norm of the test function. -/
theorem dist_integral_le (F G : C(AddCircle (1 : ℝ), ℂ)) :
    dist (∫ y, F y) (∫ y, G y) ≤ dist F G := by
  rw [dist_eq_norm, ← integral_sub (integrable_continuousMap F) (integrable_continuousMap G)]
  have h1 : ∀ᵐ y : AddCircle (1 : ℝ), ‖F y - G y‖ ≤ dist F G := by
    filter_upwards with y
    simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist y (f := F) (g := G)
  simpa [measureReal_def, AddCircle.measure_univ] using
    norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle (1 : ℝ)))) h1

theorem isClosed_weylGood : IsClosed (weylGood alpha : Set C(AddCircle (1 : ℝ), ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro F hF
  show Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y))
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨G, hG, hFG⟩ := Metric.mem_closure_iff.1 hF (eps / 3) (by linarith)
  have hGtend : Tendsto (circleAvg alpha G) atTop (𝓝 (∫ y, G y)) := hG
  rw [Metric.tendsto_atTop] at hGtend
  obtain ⟨N₀, hN₀⟩ := hGtend (eps / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  calc dist (circleAvg alpha F N) (∫ y, F y)
      ≤ dist (circleAvg alpha F N) (circleAvg alpha G N)
        + dist (circleAvg alpha G N) (∫ y, G y) + dist (∫ y, G y) (∫ y, F y) := by
        exact dist_triangle4 _ _ _ _
    _ < eps := by
        have h1 := dist_circleAvg_le alpha F G N
        have h2 := hN₀ N hN
        have h3 : dist (∫ y, G y) (∫ y, F y) ≤ dist F G := by
          rw [dist_comm]; exact dist_integral_le F G
        linarith

/-- Weyl's equidistribution theorem for continuous complex test functions. -/
theorem tendsto_circleAvg (halpha : Irrational alpha) (F : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y)) := by
  have hspan : Submodule.span ℂ (Set.range (fourier : ℤ → C(AddCircle (1 : ℝ), ℂ)))
      ≤ weylGood alpha := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact fourier_mem_weylGood alpha halpha k
  have hall := Submodule.topologicalClosure_minimal _ hspan (isClosed_weylGood alpha)
  rw [span_fourier_closure_eq_top] at hall
  exact hall (Submodule.mem_top)

/-- Weyl's equidistribution theorem for continuous real test functions. -/
theorem tendsto_circleAvg_real (halpha : Irrational alpha) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N)
      atTop (𝓝 (∫ y, f y)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    (⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f with hFdef
  have hFC : Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y)) := tendsto_circleAvg alpha halpha F
  have hint : (∫ y, F y) = ((∫ y, f y : ℝ) : ℂ) := by
    simp only [hFdef, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact integral_ofReal
  have havg : ∀ N : ℕ, circleAvg alpha F N =
      (((∑ n ∈ Finset.range N, f ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N : ℝ) : ℂ) := by
    intro N
    simp [circleAvg, hFdef]
  rw [hint] at hFC
  have := (Complex.continuous_re.tendsto _).comp hFC
  simp only [Function.comp_def, havg, Complex.ofReal_re] at this
  exact this

end Weyl

section Bump

/-- A continuous trapezoidal bump on the circle: it equals `1` on the closed ball of radius
`r - d` around `m`, vanishes outside the closed ball of radius `r`, and takes values in `[0, 1]`. -/
def bump (m r d : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun x => max 0 (min 1 ((r - dist x ((m : ℝ) : AddCircle (1 : ℝ))) / d)), by fun_prop⟩

theorem bump_nonneg (m r d : ℝ) (x : AddCircle (1 : ℝ)) : 0 ≤ bump m r d x := le_max_left _ _

theorem bump_le_one (m r d : ℝ) (x : AddCircle (1 : ℝ)) : bump m r d x ≤ 1 := by
  simp only [bump, ContinuousMap.coe_mk]
  exact max_le zero_le_one (min_le_left _ _)

theorem bump_eq_one {m r d : ℝ} (hd : 0 < d) {x : AddCircle (1 : ℝ)}
    (hx : dist x ((m : ℝ) : AddCircle (1 : ℝ)) ≤ r - d) : bump m r d x = 1 := by
  have h1 : (1 : ℝ) ≤ (r - dist x ((m : ℝ) : AddCircle (1 : ℝ))) / d := by
    rw [le_div_iff₀ hd]; linarith
  simp [bump, min_eq_left h1]

theorem bump_eq_zero {m r d : ℝ} (hd : 0 < d) {x : AddCircle (1 : ℝ)}
    (hx : r ≤ dist x ((m : ℝ) : AddCircle (1 : ℝ))) : bump m r d x = 0 := by
  have h1 : (r - dist x ((m : ℝ) : AddCircle (1 : ℝ))) / d ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [bump, ContinuousMap.coe_mk]
  rw [max_eq_left (le_trans (min_le_right _ _) h1)]

theorem integrable_bump (m r d : ℝ) : Integrable (fun y => bump m r d y) volume :=
  (bump m r d).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_bump_le (m r d : ℝ) (hd : 0 < d) (hr : 0 ≤ r) :
    ∫ y, bump m r d y ≤ 2 * r := by
  have hle : ∀ y, bump m r d y ≤
      (closedBall ((m : ℝ) : AddCircle (1 : ℝ)) r).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ closedBall ((m : ℝ) : AddCircle (1 : ℝ)) r
    · rw [Set.indicator_of_mem hy]
      exact bump_le_one m r d y
    · rw [Set.indicator_of_notMem hy]
      exact le_of_eq (bump_eq_zero hd (le_of_lt (by simpa [mem_closedBall] using hy)))
  have hint := integral_mono (integrable_bump m r d)
    ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall) hle
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, measureReal_def,
    AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))] at hint
  simp only [smul_eq_mul, mul_one] at hint
  exact le_trans hint (min_le_right _ _)

theorem le_integral_bump (m r d : ℝ) (hd : 0 < d) (hr : r ≤ 1 / 2) :
    2 * (r - d) ≤ ∫ y, bump m r d y := by
  rcases lt_or_ge (r - d) 0 with h | h
  · have hpos : (0 : ℝ) ≤ ∫ y, bump m r d y := integral_nonneg fun y => bump_nonneg m r d y
    linarith
  · have hle : ∀ y, (closedBall ((m : ℝ) : AddCircle (1 : ℝ)) (r - d)).indicator
        (fun _ => (1 : ℝ)) y ≤ bump m r d y := by
      intro y
      by_cases hy : y ∈ closedBall ((m : ℝ) : AddCircle (1 : ℝ)) (r - d)
      · rw [Set.indicator_of_mem hy]
        exact le_of_eq (bump_eq_one hd (by simpa [mem_closedBall] using hy)).symm
      · rw [Set.indicator_of_notMem hy]
        exact bump_nonneg m r d y
    have hint := integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      (integrable_bump m r d) hle
    rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, measureReal_def,
      AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by linarith)),
      min_eq_right (by linarith)] at hint
    simpa using hint

end Bump

section Sandwich

variable {alpha a b : ℝ}

/-- The circle distance between the classes of two reals, computed on representatives. -/
theorem dist_coe_eq (t m : ℝ) :
    dist ((t : ℝ) : AddCircle (1 : ℝ)) ((m : ℝ) : AddCircle (1 : ℝ))
      = |(t - m) - round (t - m)| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  simp

/-- If the fractional part of `t` lies in the window `[a, b)`, then `t` is within `(b - a)/2` of
the window's midpoint, measured on the circle. -/
theorem dist_le_of_fract_mem {t : ℝ} (ht : Int.fract t ∈ Set.Ico a b) :
    dist ((t : ℝ) : AddCircle (1 : ℝ)) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ≤ (b - a) / 2 := by
  rw [dist_coe_eq]
  have h1 : |(t - (a + b) / 2) - round (t - (a + b) / 2)| ≤ |(t - (a + b) / 2) - (⌊t⌋ : ℝ)| :=
    round_le _ _
  have h2 : (t - (a + b) / 2) - (⌊t⌋ : ℝ) = Int.fract t - (a + b) / 2 := by
    rw [Int.fract]; ring
  rw [h2] at h1
  obtain ⟨h3, h4⟩ := ht
  refine h1.trans ?_
  rw [abs_le]
  constructor <;> linarith

/-- Conversely, a point strictly within `(b - a)/2` of the midpoint has fractional part in the
window `[a, b)`. -/
theorem fract_mem_of_dist_lt (ha : 0 ≤ a) (hb : b ≤ 1) {t : ℝ}
    (ht : dist ((t : ℝ) : AddCircle (1 : ℝ)) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) < (b - a) / 2) :
    Int.fract t ∈ Set.Ico a b := by
  rw [dist_coe_eq] at ht
  set k : ℤ := round (t - (a + b) / 2) with hk
  set j : ℤ := ⌊t⌋ - k with hj
  have hfr : Int.fract t + (j : ℝ) = (t - (a + b) / 2) - k + (a + b) / 2 := by
    rw [Int.fract, hj]; push_cast; ring
  have habs := abs_lt.1 ht
  have h0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have h1 : Int.fract t < 1 := Int.fract_lt_one t
  have hj0 : j = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hjle : (j : ℝ) ≤ -1 := by exact_mod_cast (by omega : j ≤ -1)
      linarith [habs.1, hfr]
    · have hjge : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
      linarith [habs.2, hfr]
  rw [hj0] at hfr
  push_cast at hfr
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

end Sandwich

/-- The configuration count written as a sum of indicators. -/
theorem configCount_eq_sum {alpha a b : ℝ} (N : ℕ) : (configCount alpha a b N : ℝ)
    = ∑ n ∈ Finset.range N, if Int.fract ((n : ℝ) * alpha) ∈ Set.Ico a b then (1 : ℝ) else 0 := by
  rw [configCount, Finset.card_filter]
  push_cast
  rfl

/-- The count is bounded above by a Birkhoff sum of a slightly wider bump. -/
theorem configCount_le_sum_bump {alpha a b : ℝ} (d : ℝ) (hd : 0 < d) (N : ℕ) :
    (configCount alpha a b N : ℝ) ≤ ∑ n ∈ Finset.range N,
      bump ((a + b) / 2) ((b - a) / 2 + d) d ((n * alpha : ℝ) : AddCircle (1 : ℝ)) := by
  rw [configCount_eq_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hmem : Int.fract ((n : ℝ) * alpha) ∈ Set.Ico a b
  · rw [if_pos hmem]
    exact le_of_eq (bump_eq_one hd (by simpa using dist_le_of_fract_mem hmem)).symm
  · rw [if_neg hmem]
    exact bump_nonneg _ _ _ _

/-- The count is bounded below by a Birkhoff sum of a bump supported in the window. -/
theorem sum_bump_le_configCount {alpha a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (d : ℝ) (hd : 0 < d)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, bump ((a + b) / 2) ((b - a) / 2) d ((n * alpha : ℝ) : AddCircle (1 : ℝ))
      ≤ (configCount alpha a b N : ℝ) := by
  rw [configCount_eq_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hmem : Int.fract ((n : ℝ) * alpha) ∈ Set.Ico a b
  · rw [if_pos hmem]
    exact bump_le_one _ _ _ _
  · rw [if_neg hmem]
    have hdist : (b - a) / 2 ≤ dist ((n * alpha : ℝ) : AddCircle (1 : ℝ))
        (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) := by
      by_contra hcon
      exact hmem (fract_mem_of_dist_lt ha hb (lt_of_not_ge hcon))
    exact le_of_eq (bump_eq_zero hd hdist)

/-- The counting function divided by `N` tends to the window length. -/
theorem configCount_div_tendsto {alpha a b : ℝ} (halpha : Irrational alpha) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  set d : ℝ := eps / 4 with hd_def
  have hd : 0 < d := by positivity
  set r : ℝ := (b - a) / 2 with hr_def
  set m : ℝ := (a + b) / 2 with hm_def
  have hrhalf : r ≤ 1 / 2 := by rw [hr_def]; linarith
  have hr0 : 0 < r := by rw [hr_def]; linarith
  have hUint : ∫ y, (bump m (r + d) d) y ≤ 2 * (r + d) :=
    integral_bump_le m (r + d) d hd (by linarith)
  have hLint : 2 * (r - d) ≤ ∫ y, (bump m r d) y := le_integral_bump m r d hd hrhalf
  have hUtend := tendsto_circleAvg_real alpha halpha (bump m (r + d) d)
  have hLtend := tendsto_circleAvg_real alpha halpha (bump m r d)
  rw [Metric.tendsto_atTop] at hUtend hLtend
  obtain ⟨N1, hN1⟩ := hUtend d hd
  obtain ⟨N2, hN2⟩ := hLtend d hd
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1 := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  have hup := configCount_le_sum_bump (alpha := alpha) (a := a) (b := b) d hd N
  have hlo := sum_bump_le_configCount (alpha := alpha) (a := a) (b := b) ha hb d hd N
  rw [← hr_def, ← hm_def] at hup hlo
  have hupdiv : (configCount alpha a b N : ℝ) / N
      ≤ (∑ n ∈ Finset.range N, (bump m (r + d) d) ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N := by
    gcongr
  have hlodiv : (∑ n ∈ Finset.range N, (bump m r d) ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N
      ≤ (configCount alpha a b N : ℝ) / N := by
    gcongr
  have h2r : 2 * r = b - a := by rw [hr_def]; ring
  constructor
  · linarith [h2.1, hLint, hlodiv]
  · linarith [h1.2, hUint, hupdiv]

/-- **Equidistribution / BV reduction.** For irrational `alpha` and a window `[a, b) ⊆ [0, 1]` of
positive length, the number of `n < N` with `Int.fract (n * alpha) ∈ [a, b)` is asymptotic to the
main term `(b - a) * N`. -/
theorem configCount_over_main_tendsto {alpha a b : ℝ} (halpha : Irrational alpha) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / mainTerm a b N) atTop (𝓝 1) := by
  have hba : b - a ≠ 0 := by linarith
  have h := (configCount_div_tendsto halpha ha hab hb).div_const (b - a)
  rw [div_self hba] at h
  refine h.congr fun N => ?_
  rw [mainTerm, div_div, mul_comm]

end

end Brockian.EquidistributionBVReduction

