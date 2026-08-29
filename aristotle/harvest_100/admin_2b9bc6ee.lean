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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/
noncomputable def weylAvg (α : ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))

theorem circle_integrable (f : C(AddCircle (1 : ℝ), ℂ)) : Integrable (fun x => f x) volume :=
  Continuous.integrable_of_hasCompactSupport f.continuous (HasCompactSupport.of_compactSpace _)

theorem weylAvg_sub_le (α : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖weylAvg α f N - weylAvg α g N‖ ≤ ‖f - g‖ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [weylAvg]
  have h1 : weylAvg α f N - weylAvg α g N
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [weylAvg, ContinuousMap.sub_apply, Finset.sum_sub_distrib]
    ring
  rw [h1, norm_mul, norm_inv, Complex.norm_natCast]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : ‖∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖
      ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖
        ≤ ∑ n ∈ Finset.range N, ‖(f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ :=
          Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm _ _
      _ = N * ‖f - g‖ := by simp
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖
      ≤ (N : ℝ)⁻¹ * (N * ‖f - g‖) := by gcongr
    _ = ‖f - g‖ := by field_simp

theorem circle_integral_sub_le (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ x, f x) - ∫ x, g x‖ ≤ ‖f - g‖ := by
  have h : (∫ x, f x) - (∫ x, g x) = ∫ x, (f - g) x := by
    rw [← integral_sub (circle_integrable f) (circle_integrable g)]; simp
  rw [h]
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle (1 : ℝ))))
    (f := fun x => (f - g) x) (C := ‖f - g‖)
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm _ _)
  simpa [measureReal_def] using this

/-- The set of continuous functions whose Weyl averages converge to their integral. -/
noncomputable def weylGood (α : ℝ) : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) where
  carrier := {f | Tendsto (weylAvg α f) atTop (𝓝 (∫ x, f x))}
  zero_mem' := by
    have h : weylAvg α 0 = fun _ : ℕ => (0 : ℂ) := by funext N; simp [weylAvg]
    simp only [Set.mem_setOf_eq, h]
    simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ x, (f + g) x = (∫ x, f x) + ∫ x, g x := by
      simpa using integral_add (circle_integrable f) (circle_integrable g)
    have heq : weylAvg α (f + g) = fun N => weylAvg α f N + weylAvg α g N := by
      funext N; simp [weylAvg, Finset.sum_add_distrib, mul_add]
    rw [hint, heq]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ x, (c • f) x = c * ∫ x, f x := by
      simpa [smul_eq_mul] using integral_smul c fun x => f x
    have heq : weylAvg α (c • f) = fun N => c * weylAvg α f N := by
      funext N
      simp only [weylAvg, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [hint, heq]
    exact hf.const_mul c

theorem weylGood_closed (α : ℝ) :
    IsClosed ((weylGood α : Submodule ℂ C(AddCircle (1 : ℝ), ℂ)) :
      Set C(AddCircle (1 : ℝ), ℂ)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  show Tendsto (weylAvg α f) atTop (𝓝 (∫ x, f x))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by linarith)
  have hgmem : Tendsto (weylAvg α g) atTop (𝓝 (∫ x, g x)) := hgS
  rw [Metric.tendsto_atTop] at hgmem
  obtain ⟨N₀, hN₀⟩ := hgmem (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have hnorm : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hnorm' : ‖g - f‖ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hfg
  have d1 : dist (weylAvg α f N) (weylAvg α g N) < ε / 3 := by
    rw [dist_eq_norm]; linarith [weylAvg_sub_le α f g N]
  have d3 : dist (∫ x, g x) (∫ x, f x) < ε / 3 := by
    rw [dist_eq_norm]; linarith [circle_integral_sub_le g f]
  have d2 := hN₀ N hN
  calc dist (weylAvg α f N) (∫ x, f x)
      ≤ dist (weylAvg α f N) (weylAvg α g N) + dist (weylAvg α g N) (∫ x, g x)
        + dist (∫ x, g x) (∫ x, f x) := dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-! ## The Weyl exponential sums -/

theorem exp_ne_one_of_irrational {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    Complex.exp (2 * (Real.pi : ℂ) * I * k * α) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (k : ℂ) * α = n := by field_simp at hn; linear_combination hn
  have h4 : (k : ℝ) * α = (n : ℝ) := by exact_mod_cast h2
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  refine hα ⟨(n : ℚ) / (k : ℚ), ?_⟩
  push_cast
  field_simp
  linarith [h4]

theorem tendsto_weylAvg_fourier_ne_zero (α : ℝ) {k : ℤ}
    (hz : Complex.exp (2 * (Real.pi : ℂ) * I * k * α) ≠ 1) :
    Tendsto (weylAvg α (fourier k)) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * k * α) with hzdef
  have habs : ‖z‖ = 1 := by rw [hzdef, Complex.norm_exp]; simp
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      fourier k (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) = (z ^ N - 1) / (z - 1) := by
    intro N
    rw [← geom_sum_eq hz]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourier_coe_apply, hzdef, ← Complex.exp_nat_mul]
    push_cast; ring_nf
  have hden : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hbound : ∀ N : ℕ, ‖weylAvg α (fourier k) N‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    have h2 : ‖z ^ N - 1‖ ≤ 2 :=
      calc ‖z ^ N - 1‖ ≤ ‖(z : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, habs]; norm_num
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [weylAvg]
    · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      rw [weylAvg, hsum N, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
      calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) = ‖z ^ N - 1‖ / (‖z - 1‖ * N) := by ring
        _ ≤ 2 / (‖z - 1‖ * N) := by gcongr
        _ = (2 / ‖z - 1‖) / N := by ring
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

theorem integral_fourier_ne_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x : AddCircle (1 : ℝ), fourier k x = 0 := by
  have hc : (2 * (Real.pi : ℂ) * I * (k : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero, hk]
  have hfun : ∀ x : ℝ, fourier k ((x : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp ((2 * (Real.pi : ℂ) * I * (k : ℂ)) * x) := by
    intro x
    rw [fourier_coe_apply]
    norm_num
  rw [← AddCircle.integral_preimage (1 : ℝ) 0, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_congr
      (g := fun x : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * I * (k : ℂ)) * x))
      fun x _ => hfun x,
    integral_exp_mul_complex hc]
  have h : (2 * (Real.pi : ℂ) * I * (k : ℂ)) * ((0 : ℝ) + 1 : ℝ) = (k : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem fourier_mem_weylGood {α : ℝ} (hα : Irrational α) (k : ℤ) : fourier k ∈ weylGood α := by
  rcases eq_or_ne k 0 with rfl | hk
  · show Tendsto (weylAvg α (fourier 0)) atTop (𝓝 (∫ x : AddCircle (1 : ℝ), (fourier 0) x))
    have hint : (∫ x : AddCircle (1 : ℝ), (fourier (T := (1 : ℝ)) 0) x) = 1 := by
      simp [measureReal_def]
    rw [hint]
    have hval : ∀ N : ℕ, 1 ≤ N → weylAvg α (fourier (T := (1 : ℝ)) 0) N = 1 := by
      intro N hN
      simp only [weylAvg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    exact Tendsto.congr'
      (by filter_upwards [eventually_ge_atTop 1] with N hN using (hval N hN).symm)
      tendsto_const_nhds
  · show Tendsto (weylAvg α (fourier k)) atTop (𝓝 (∫ x : AddCircle (1 : ℝ), (fourier k) x))
    rw [integral_fourier_ne_zero hk]
    exact tendsto_weylAvg_fourier_ne_zero α (exp_ne_one_of_irrational hα hk)

/-- **Weyl's equidistribution theorem, test-function form.** For irrational `α` and any
continuous complex-valued function `f` on the circle `ℝ / ℤ`, the averages of `f` along the
orbit `n ↦ nα` converge to the integral of `f`. -/
theorem tendsto_weylAvg {α : ℝ} (hα : Irrational α) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (weylAvg α f) atTop (𝓝 (∫ x, f x)) := by
  have hle : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ weylGood α := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact fourier_mem_weylGood hα k
  have hsub := Submodule.topologicalClosure_minimal _ hle (weylGood_closed α)
  exact hsub (by rw [span_fourier_closure_eq_top]; trivial)

/-- Real-valued version of `tendsto_weylAvg`. -/
theorem tendsto_weylAvg_real {α : ℝ} (hα : Irrational α) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ =>
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)))
      atTop (𝓝 (∫ x, f x)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hint : (∫ x, F x) = ((∫ x, f x : ℝ) : ℂ) := integral_complex_ofReal
  have havg : ∀ N : ℕ, weylAvg α F N
      = (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          f (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
    intro N
    simp [weylAvg, hF]
  have h := tendsto_weylAvg hα F
  rw [hint] at h
  exact tendsto_ofReal_iff.mp (h.congr havg)

/-! ## Trapezoidal test functions -/

/-- The trapezoidal function which is `1` on `[a + δ, b - δ]`, `0` outside `(a, b)`, and
interpolates linearly in between. -/
noncomputable def trap (a b δ : ℝ) (x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - a) / δ) ((b - x) / δ)))

theorem trap_continuous (a b δ : ℝ) : Continuous (trap a b δ) := by unfold trap; fun_prop

theorem trap_nonneg (a b δ x : ℝ) : 0 ≤ trap a b δ x := le_max_left _ _

theorem trap_le_one (a b δ x : ℝ) : trap a b δ x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem trap_eq_zero_of_le (a b δ x : ℝ) (hδ : 0 < δ) (h : x ≤ a) : trap a b δ x = 0 :=
  max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)))

theorem trap_eq_zero_of_ge (a b δ x : ℝ) (hδ : 0 < δ) (h : b ≤ x) : trap a b δ x = 0 :=
  max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)))

theorem trap_eq_one (a b δ x : ℝ) (hδ : 0 < δ) (h1 : a + δ ≤ x) (h2 : x ≤ b - δ) :
    trap a b δ x = 1 := by
  have e1 : 1 ≤ (x - a) / δ := by rw [le_div_iff₀ hδ]; linarith
  have e2 : 1 ≤ (b - x) / δ := by rw [le_div_iff₀ hδ]; linarith
  unfold trap
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

theorem trap_integral_ge (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a + δ ≤ b - δ) : (b - a) - 2 * δ ≤ ∫ x in (0 : ℝ)..1, trap a b δ x := by
  have hc : Continuous (trap a b δ) := trap_continuous a b δ
  have hint : ∀ u v : ℝ, IntervalIntegrable (trap a b δ) volume u v :=
    fun u v => hc.intervalIntegrable u v
  have h1 : (0 : ℝ) ≤ a + δ := by linarith
  have h2 : b - δ ≤ 1 := by linarith
  have hsplit : (∫ x in (0 : ℝ)..1, trap a b δ x)
      = (∫ x in (0 : ℝ)..(a + δ), trap a b δ x) + (∫ x in (a + δ)..(b - δ), trap a b δ x)
        + ∫ x in (b - δ)..1, trap a b δ x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmid : (∫ x in (a + δ)..(b - δ), trap a b δ x) = (b - δ) - (a + δ) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
    · simp
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact trap_eq_one a b δ x hδ hx.1 hx.2
  have hl : 0 ≤ ∫ x in (0 : ℝ)..(a + δ), trap a b δ x :=
    intervalIntegral.integral_nonneg h1 fun x _ => trap_nonneg _ _ _ _
  have hr : 0 ≤ ∫ x in (b - δ)..1, trap a b δ x :=
    intervalIntegral.integral_nonneg h2 fun x _ => trap_nonneg _ _ _ _
  rw [hsplit, hmid]
  linarith

/-- The trapezoidal function, viewed as a continuous function on the circle `ℝ / ℤ`. -/
noncomputable def trapCM (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    C(AddCircle (1 : ℝ), ℝ) :=
  ⟨AddCircle.liftIco 1 0 (trap a b δ),
    AddCircle.liftIco_zero_continuous
      (by rw [trap_eq_zero_of_le a b δ 0 hδ ha, trap_eq_zero_of_ge a b δ 1 hδ hb])
      (trap_continuous a b δ).continuousOn⟩

theorem trapCM_integral (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    (∫ x : AddCircle (1 : ℝ), trapCM a b δ hδ ha hb x) = ∫ x in (0 : ℝ)..1, trap a b δ x := by
  have hf : trap a b δ 0 = trap a b δ (0 + 1) := by
    rw [zero_add, trap_eq_zero_of_le a b δ 0 hδ ha, trap_eq_zero_of_ge a b δ 1 hδ hb]
  show (∫ x : AddCircle (1 : ℝ), AddCircle.liftIco 1 0 (trap a b δ) x) = _
  rw [← AddCircle.liftIoc_eq_liftIco hf, AddCircle.integral_liftIoc_eq_intervalIntegral]
  norm_num

theorem trapCM_apply (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    trapCM a b δ hδ ha hb ((x : ℝ) : AddCircle (1 : ℝ)) = trap a b δ x := by
  show AddCircle.liftIco 1 0 (trap a b δ) ((x : ℝ) : AddCircle (1 : ℝ)) = _
  exact AddCircle.liftIco_zero_coe_apply hx

theorem coe_eq_coe_fract (x : ℝ) :
    ((x : ℝ) : AddCircle (1 : ℝ)) = ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) := by
  have h0 : (((⌊x⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨⌊x⌋, by simp⟩
  have h1 : ((Int.fract x : ℝ) : AddCircle (1 : ℝ))
      = (x : AddCircle (1 : ℝ)) - (((⌊x⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [Int.fract]
    exact QuotientAddGroup.mk_sub _ _ _
  rw [h1, h0, sub_zero]

/-! ## Counting visits to an interval -/

/-- The number of `n < N` for which the fractional part of `n * α` lies in `[a, b)`. -/
noncomputable def countIco (α a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n : ℕ =>
    a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b).card

theorem sum_trap_le_count (α a b δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∑ n ∈ Finset.range N, trap a b δ (Int.fract ((n : ℝ) * α)) ≤ (countIco α a b N : ℝ) := by
  classical
  have hcard : (countIco α a b N : ℝ)
      = ∑ n ∈ Finset.range N,
          if a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b then (1 : ℝ) else 0 := by
    unfold countIco
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases h : a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b
  · simp [h, trap_le_one]
  · rw [if_neg h]
    push_neg at h
    rcases lt_or_ge (Int.fract ((n : ℝ) * α)) a with h1 | h1
    · rw [trap_eq_zero_of_le a b δ _ hδ h1.le]
    · rw [trap_eq_zero_of_ge a b δ _ hδ (h h1)]

theorem count_partition (α : ℝ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    countIco α 0 a N + countIco α a b N + countIco α b 1 N = N := by
  classical
  unfold countIco
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine (Finset.sum_eq_card_nsmul (b := (1 : ℕ)) fun n _ => ?_).trans (by simp)
  have h0 := Int.fract_nonneg ((n : ℝ) * α)
  have h1 := Int.fract_lt_one ((n : ℝ) * α)
  rcases lt_or_ge (Int.fract ((n : ℝ) * α)) a with hA | hA
  · rw [if_pos ⟨h0, hA⟩, if_neg (by push_neg; intro h; linarith),
      if_neg (by push_neg; intro h; linarith)]
  · rcases lt_or_ge (Int.fract ((n : ℝ) * α)) b with hB | hB
    · rw [if_neg (by push_neg; intro _; linarith), if_pos ⟨hA, hB⟩,
        if_neg (by push_neg; intro h; linarith)]
    · rw [if_neg (by push_neg; intro _; linarith), if_neg (by push_neg; intro _; linarith),
        if_pos ⟨hB, h1⟩]

/-- Lower bound: asymptotically, the orbit visits `[a, b)` at least a `(b - a) - ε` fraction of
the time. -/
theorem count_eventually_ge {α : ℝ} (hα : Irrational α) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (b - a) - ε ≤ (countIco α a b N : ℝ) / N := by
  rcases le_or_gt (b - a) ε with hcase | hcase
  · filter_upwards with N
    have h : (0 : ℝ) ≤ (countIco α a b N : ℝ) / N := by positivity
    linarith
  set δ : ℝ := min (ε / 4) ((b - a) / 4) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ε / 4 := min_le_left _ _
  have hδ2 : δ ≤ (b - a) / 4 := min_le_right _ _
  have hmid : a + δ ≤ b - δ := by linarith
  set g : C(AddCircle (1 : ℝ), ℝ) := trapCM a b δ hδ ha hb with hg
  have hI : (b - a) - 2 * δ ≤ ∫ x, g x := by
    rw [hg, trapCM_integral]
    exact trap_integral_ge a b δ hδ ha hb hmid
  have htend := tendsto_weylAvg_real hα g
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend δ hδ
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hd := hN₀ N hN
  rw [Real.dist_eq, abs_lt] at hd
  have havg : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, g (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, trap a b δ (Int.fract ((n : ℝ) * α)) := by
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coe_eq_coe_fract, hg,
      trapCM_apply a b δ hδ ha hb _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩]
  have hle : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, trap a b δ (Int.fract ((n : ℝ) * α))
      ≤ (countIco α a b N : ℝ) / N := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (sum_trap_le_count α a b δ hδ N) (by positivity)
  rw [havg] at hd
  linarith [hd.1, hle]

/-! ## The main theorem -/

/-- **Weyl's equidistribution theorem.** For every irrational `α` and every subinterval
`[a, b) ⊆ [0, 1]`, the proportion of the first `N` points of the sequence of fractional parts
`(fract (n α))ₙ` that lie in `[a, b)` converges to the length `b - a` of the interval.

In particular the asymptotic frequency exists (and is unconditional: no hypothesis beyond the
irrationality of `α` is assumed). -/
theorem equidistribution_of_asymptotic_exists {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  show Tendsto (fun N : ℕ => (countIco α a b N : ℝ) / N) atTop (𝓝 (b - a))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have E1 := count_eventually_ge hα ha hb (ε := ε / 4) (by linarith)
  have E2 := count_eventually_ge hα le_rfl (le_trans hab hb) (ε := ε / 4) (by linarith)
  have E3 := count_eventually_ge hα (le_trans ha hab) (le_refl (1 : ℝ)) (ε := ε / 4) (by linarith)
  have hev : ∀ᶠ N : ℕ in atTop, dist ((countIco α a b N : ℝ) / N) (b - a) < ε := by
    filter_upwards [E1, E2, E3, eventually_ge_atTop 1] with N h1 h2 h3 hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum : ((countIco α 0 a N : ℝ) / N) + ((countIco α a b N : ℝ) / N)
        + ((countIco α b 1 N : ℝ) / N) = 1 := by
      have hp := count_partition α hab N
      field_simp
      exact_mod_cast hp
    rw [Real.dist_eq, abs_lt]
    constructor <;> simp only [sub_lt_iff_lt_add, lt_sub_iff_add_lt] <;> linarith
  rw [eventually_atTop] at hev
  exact hev

/-- Sanity check: the hypotheses of the main theorem are satisfiable, e.g. for `α = √2` and the
interval `[0, 1/2)`. -/
example :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            (0 : ℝ) ≤ Int.fract ((n : ℝ) * Real.sqrt 2) ∧
              Int.fract ((n : ℝ) * Real.sqrt 2) < 1 / 2).card : ℝ) / N)
      atTop (𝓝 (1 / 2 - 0)) :=
  equidistribution_of_asymptotic_exists irrational_sqrt_two le_rfl (by norm_num) (by norm_num)

end Brockian.Equidistribution

