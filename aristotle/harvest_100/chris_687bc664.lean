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
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The block above is repeated as the file header; Lean does not allow a module docstring to
precede the `import` line.)

This file proves **Weyl's equidistribution criterion** unconditionally: if all nontrivial
exponential sums of a real sequence `x` are asymptotically negligible, then `x` is
equidistributed modulo one.  The argument goes through the circle `𝕋 = AddCircle 1`:

* the Birkhoff averages of each Fourier monomial converge to its integral (`avgC_fourier_tendsto`);
* the set of continuous functions with this property is a closed submodule of `C(𝕋, ℂ)`, hence,
  by Stone-Weierstrass (`span_fourier_closure_eq_top`), is everything (`avgC_tendsto`);
* indicator functions of arcs are squeezed between continuous plateau functions supported on
  metric balls, whose integrals are controlled by `AddCircle.volume_closedBall`.

As an application (and as a witness that the hypothesis is satisfiable) we derive the classical
equidistribution of irrational rotations, `equidistribution_irrational_rotation`.
-/

open Filter MeasureTheory Metric Complex Set
open scoped Topology Real BigOperators

namespace Brockian.Equidistribution

local notation "𝕋" => AddCircle (1 : ℝ)

/-- The Birkhoff/Weyl average of a complex-valued continuous function on the circle along the
first `N` terms of the sequence `x`. -/
noncomputable def avgC (x : ℕ → ℝ) (F : C(𝕋, ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, F ((x n : ℝ) : 𝕋)

/-- The Birkhoff/Weyl average of a real-valued continuous function on the circle. -/
noncomputable def avgR (x : ℕ → ℝ) (G : C(𝕋, ℝ)) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, G ((x n : ℝ) : 𝕋)

/-- On the circle of circumference one, the normalised Haar measure is the standard volume. -/
lemma haar_eq_volume : (AddCircle.haarAddCircle (T := (1 : ℝ))) = (volume : Measure 𝕋) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

lemma contMap_integrable (G : C(𝕋, ℝ)) :
    Integrable (fun z => G z) (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma contMapC_integrable (F : C(𝕋, ℂ)) :
    Integrable (fun z => F z) (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Step A: the Fourier monomials -/

lemma integral_fourier (k : ℤ) :
    ∫ z : 𝕋, fourier k z ∂AddCircle.haarAddCircle = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [h]
  by_cases hk : k = 0 <;> simp [hk, Pi.single_apply, eq_comm]

lemma avgC_fourier_tendsto (x : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * x n)) atTop (𝓝 0)) (k : ℤ) :
    Tendsto (avgC x (fourier k)) atTop
      (𝓝 (∫ z : 𝕋, fourier k z ∂AddCircle.haarAddCircle)) := by
  rw [integral_fourier]
  by_cases hk : k = 0
  · subst hk
    have : ∀ N : ℕ, 1 ≤ N → avgC x (fourier 0) N = 1 := by
      intro N hN
      simp only [avgC, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [inv_mul_cancel₀]
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using (this N hN).symm
  · simp only [if_neg hk]
    have hEq : ∀ N : ℕ, avgC x (fourier k) N
        = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * k * x n) := by
      intro N
      simp [avgC]
    exact (hW k hk).congr fun N => (hEq N).symm

/-! ### Step B: all continuous functions -/

lemma avgC_sub (x : ℕ → ℝ) (F G : C(𝕋, ℂ)) (N : ℕ) :
    avgC x F N - avgC x G N = avgC x (F - G) N := by
  simp only [avgC, ContinuousMap.sub_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]

lemma norm_avgC_le (x : ℕ → ℝ) (F : C(𝕋, ℂ)) (N : ℕ) : ‖avgC x F N‖ ≤ ‖F‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [avgC, norm_nonneg F]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ‖∑ n ∈ Finset.range N, F ((x n : ℝ) : 𝕋)‖ ≤ N * ‖F‖ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ Finset.range N, ‖F ((x n : ℝ) : 𝕋)‖
          ≤ ∑ _n ∈ Finset.range N, ‖F‖ :=
            Finset.sum_le_sum fun n _ => F.norm_coe_le_norm _
        _ = N * ‖F‖ := by simp [Finset.sum_const, nsmul_eq_mul]
    rw [avgC, norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, F ((x n : ℝ) : 𝕋)‖
        ≤ (N : ℝ)⁻¹ * (N * ‖F‖) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖F‖ := by field_simp

lemma norm_integral_le_norm (F : C(𝕋, ℂ)) :
    ‖∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖ ≤ ‖F‖ := by
  have := norm_integral_le_of_norm_le_const
    (μ := (AddCircle.haarAddCircle (T := (1 : ℝ)))) (C := ‖F‖)
    (Filter.Eventually.of_forall fun z => F.norm_coe_le_norm z)
  simpa using this

/-- The set of continuous functions whose Birkhoff averages along `x` converge to their
integral, as a `ℂ`-submodule of `C(𝕋, ℂ)`. -/
noncomputable def goodSubmodule (x : ℕ → ℝ) : Submodule ℂ C(𝕋, ℂ) where
  carrier := {F | Tendsto (avgC x F) atTop (𝓝 (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle))}
  add_mem' := by
    intro F G hF hG
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ z : 𝕋, (F + G) z ∂AddCircle.haarAddCircle
        = (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle) + ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (contMapC_integrable F) (contMapC_integrable G)
    rw [hint]
    have hA : ∀ N, avgC x (F + G) N = avgC x F N + avgC x G N := by
      intro N
      simp only [avgC, ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
    exact (hF.add hG).congr fun N => (hA N).symm
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ContinuousMap.zero_apply, integral_zero]
    have h0 : ∀ N, avgC x (0 : C(𝕋, ℂ)) N = 0 := by intro N; simp [avgC]
    exact tendsto_const_nhds.congr fun N => (h0 N).symm
  smul_mem' := by
    intro c F hF
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ z : 𝕋, (c • F) z ∂AddCircle.haarAddCircle
        = c * ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    rw [hint]
    have hA : ∀ N, avgC x (c • F) N = c * avgC x F N := by
      intro N
      simp only [avgC, ContinuousMap.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    exact (hF.const_mul c).congr fun N => (hA N).symm

lemma isClosed_goodSubmodule (x : ℕ → ℝ) :
    IsClosed ((goodSubmodule x : Submodule ℂ C(𝕋, ℂ)) : Set C(𝕋, ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro F hF
  show Tendsto (avgC x F) atTop (𝓝 (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨G, hGmem, hGdist⟩ := Metric.mem_closure_iff.1 hF (ε / 3) (by linarith)
  have hGgood : Tendsto (avgC x G) atTop (𝓝 (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)) := hGmem
  rw [Metric.tendsto_atTop] at hGgood
  obtain ⟨N₀, hN₀⟩ := hGgood (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖avgC x F N - avgC x G N‖ ≤ ‖F - G‖ := by
    rw [avgC_sub]; exact norm_avgC_le x (F - G) N
  have h2 : ‖(∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)
      - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle‖ ≤ ‖F - G‖ := by
    have : (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)
        - (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
        = ∫ z : 𝕋, (F - G) z ∂AddCircle.haarAddCircle := by
      simp only [ContinuousMap.sub_apply]
      exact (integral_sub (contMapC_integrable F) (contMapC_integrable G)).symm
    rw [this]
    exact norm_integral_le_norm (F - G)
  have hFG : ‖F - G‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hGdist
  have h3 := hN₀ N hN
  rw [dist_eq_norm] at h3 ⊢
  calc ‖avgC x F N - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖
      = ‖(avgC x F N - avgC x G N) + (avgC x G N - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
          + ((∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
              - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)‖ := by ring_nf
    _ ≤ ‖(avgC x F N - avgC x G N) + (avgC x G N - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)‖
          + ‖(∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
              - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖ := norm_add_le _ _
    _ ≤ ‖avgC x F N - avgC x G N‖ + ‖avgC x G N - ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle‖
          + ‖(∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)
              - ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle‖ := by
          gcongr; exact norm_add_le _ _
    _ < ε := by
          rw [norm_sub_rev (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)] at *
          linarith

lemma avgC_tendsto (x : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * x n)) atTop (𝓝 0)) (F : C(𝕋, ℂ)) :
    Tendsto (avgC x F) atTop (𝓝 (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle)) := by
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ goodSubmodule x := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact avgC_fourier_tendsto x hW k
  have hclosure := Submodule.topologicalClosure_minimal _ hspan (isClosed_goodSubmodule x)
  rw [span_fourier_closure_eq_top] at hclosure
  exact hclosure (Submodule.mem_top)

lemma avgR_tendsto (x : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * x n)) atTop (𝓝 0)) (G : C(𝕋, ℝ)) :
    Tendsto (avgR x G) atTop (𝓝 (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)) := by
  set F : C(𝕋, ℂ) := ⟨fun z => (G z : ℂ), Complex.continuous_ofReal.comp G.continuous⟩ with hFdef
  have h := avgC_tendsto x hW F
  have hI : ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle
      = ((∫ z : 𝕋, G z ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
    simp only [hFdef, ContinuousMap.coe_mk]
    exact integral_ofReal
  have hA : ∀ N, avgC x F N = ((avgR x G N : ℝ) : ℂ) := by
    intro N
    simp only [avgC, avgR, hFdef, ContinuousMap.coe_mk]
    push_cast
    ring
  rw [hI] at h
  have h' : Tendsto (fun N => ((avgR x G N : ℝ) : ℂ)) atTop
      (𝓝 ((∫ z : 𝕋, G z ∂AddCircle.haarAddCircle : ℝ) : ℂ)) := h.congr hA
  have h2 := (Complex.continuous_re.tendsto _).comp h'
  simpa [Function.comp_def] using h2

/-! ### Step C: plateau functions on the circle -/

/-- A continuous "plateau" function on the circle: it equals `1` on the closed ball of radius
`s - d` around `c`, vanishes outside the closed ball of radius `s`, and takes values in `[0,1]`. -/
noncomputable def bumpFn (c s d : ℝ) : C(𝕋, ℝ) :=
  ⟨fun z => min 1 (max 0 ((s - ‖z - (c : 𝕋)‖) / d)), by
    have h1 : Continuous fun z : 𝕋 => ‖z - (c : 𝕋)‖ :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    exact continuous_const.min (continuous_const.max ((continuous_const.sub h1).div_const d))⟩

lemma bumpFn_nonneg (c s d : ℝ) (z : 𝕋) : 0 ≤ bumpFn c s d z :=
  le_min zero_le_one (le_max_left _ _)

lemma bumpFn_le_one (c s d : ℝ) (z : 𝕋) : bumpFn c s d z ≤ 1 := min_le_left _ _

lemma bumpFn_eq_one {c s d : ℝ} (hd : 0 < d) {z : 𝕋} (hz : ‖z - (c : 𝕋)‖ ≤ s - d) :
    bumpFn c s d z = 1 := by
  have h : 1 ≤ (s - ‖z - (c : 𝕋)‖) / d := by
    rw [le_div_iff₀ hd]; linarith
  simp only [bumpFn, ContinuousMap.coe_mk]
  exact min_eq_left (le_max_of_le_right h)

lemma bumpFn_eq_zero {c s d : ℝ} (hd : 0 < d) {z : 𝕋} (hz : s ≤ ‖z - (c : 𝕋)‖) :
    bumpFn c s d z = 0 := by
  have h : (s - ‖z - (c : 𝕋)‖) / d ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [bumpFn, ContinuousMap.coe_mk]
  rw [max_eq_left h, min_eq_right zero_le_one]

/-! ### Integral bounds -/

lemma integral_le_measure {G : C(𝕋, ℝ)} {A : Set 𝕋} (hA : MeasurableSet A)
    (h0 : ∀ z, z ∉ A → G z = 0) (h1 : ∀ z, G z ≤ 1) :
    ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle
      ≤ (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal := by
  have hint := contMap_integrable G
  rw [← integral_add_compl hA hint]
  have hc : ∫ z in Aᶜ, G z ∂AddCircle.haarAddCircle = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => h0 z ?_
    simpa using hz
  rw [hc, add_zero]
  calc ∫ z in A, G z ∂AddCircle.haarAddCircle
      ≤ ∫ _z in A, (1 : ℝ) ∂AddCircle.haarAddCircle := by
        refine setIntegral_mono_on hint.integrableOn ((integrable_const (1 : ℝ)).integrableOn) hA
          fun z _ => h1 z
    _ = (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal := by
        simp [measureReal_def]

lemma measure_le_integral {G : C(𝕋, ℝ)} {A : Set 𝕋} (hA : MeasurableSet A)
    (h1 : ∀ z ∈ A, 1 ≤ G z) (hnn : ∀ z, 0 ≤ G z) :
    (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal
      ≤ ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle := by
  have hint := contMap_integrable G
  rw [← integral_add_compl hA hint]
  have hc : 0 ≤ ∫ z in Aᶜ, G z ∂AddCircle.haarAddCircle :=
    setIntegral_nonneg hA.compl fun z _ => hnn z
  have hb : (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal
      ≤ ∫ z in A, G z ∂AddCircle.haarAddCircle := by
    calc (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal
        = ∫ _z in A, (1 : ℝ) ∂AddCircle.haarAddCircle := by simp [measureReal_def]
      _ ≤ ∫ z in A, G z ∂AddCircle.haarAddCircle :=
          setIntegral_mono_on ((integrable_const (1 : ℝ)).integrableOn) hint.integrableOn hA h1
  linarith

lemma haar_closedBall (c : 𝕋) (r : ℝ) :
    (AddCircle.haarAddCircle (T := (1 : ℝ)) (closedBall c r)).toReal
      = max (min 1 (2 * r)) 0 := by
  rw [haar_eq_volume, AddCircle.volume_closedBall, ENNReal.toReal_ofReal']

/-! ### Arcs versus balls -/

lemma coe_sub_coe (t c : ℝ) : ((t : 𝕋) - (c : 𝕋)) = ((t - c : ℝ) : 𝕋) :=
  (AddCircle.coe_sub 1 t c).symm

lemma norm_le_of_fract_mem {a b t : ℝ}
    (ht : Int.fract t ∈ Set.Ico a b) :
    ‖((t : 𝕋) - (((a + b) / 2 : ℝ) : 𝕋))‖ ≤ (b - a) / 2 := by
  rw [coe_sub_coe, UnitAddCircle.norm_eq]
  refine (round_le (t - (a + b) / 2) ⌊t⌋).trans ?_
  obtain ⟨h1, h2⟩ := ht
  rw [Int.fract] at h1 h2
  rw [abs_le]
  constructor <;> [linarith; linarith]

lemma fract_mem_of_norm_lt {a b t : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (ht : ‖((t : 𝕋) - (((a + b) / 2 : ℝ) : 𝕋))‖ < (b - a) / 2) :
    Int.fract t ∈ Set.Ico a b := by
  rw [coe_sub_coe, UnitAddCircle.norm_eq] at ht
  set m : ℤ := round (t - (a + b) / 2) with hm
  rw [abs_lt] at ht
  obtain ⟨h1, h2⟩ := ht
  have hfl : ⌊t⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨by linarith, by linarith⟩
  rw [Int.fract, hfl]
  constructor <;> [linarith; linarith]

/-! ### Squeezing the counting function between two plateau averages -/

lemma sum_ite_eq_card (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0)
      = (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
  simp

lemma avgR_bumpLower_le (x : ℕ → ℝ) {a b d : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hd : 0 < d) (N : ℕ) :
    avgR x (bumpFn ((a + b) / 2) ((b - a) / 2) d) N
      ≤ (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N := by
  have hpt : ∀ n ∈ Finset.range N,
      (bumpFn ((a + b) / 2) ((b - a) / 2) d) ((x n : ℝ) : 𝕋)
        ≤ (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
    intro n _
    by_cases hn : Int.fract (x n) ∈ Set.Ico a b
    · rw [if_pos hn]; exact bumpFn_le_one _ _ _ _
    · rw [if_neg hn]
      refine le_of_eq (bumpFn_eq_zero hd ?_)
      by_contra hcon
      push_neg at hcon
      exact hn (fract_mem_of_norm_lt ha hb hcon)
  have hsum := Finset.sum_le_sum hpt
  have hdiv : (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
    rw [sum_ite_eq_card x a b N]; ring
  rw [avgR, hdiv]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

lemma le_avgR_bumpUpper (x : ℕ → ℝ) {a b d : ℝ} (hd : 0 < d) (N : ℕ) :
    (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N
      ≤ avgR x (bumpFn ((a + b) / 2) ((b - a) / 2 + d) d) N := by
  have hpt : ∀ n ∈ Finset.range N,
      (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0)
        ≤ (bumpFn ((a + b) / 2) ((b - a) / 2 + d) d) ((x n : ℝ) : 𝕋) := by
    intro n _
    by_cases hn : Int.fract (x n) ∈ Set.Ico a b
    · rw [if_pos hn]
      have hnorm := norm_le_of_fract_mem hn
      exact le_of_eq (bumpFn_eq_one hd (by linarith)).symm
    · rw [if_neg hn]; exact bumpFn_nonneg _ _ _ _
  have hsum := Finset.sum_le_sum hpt
  have hdiv : (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
    rw [sum_ite_eq_card x a b N]; ring
  rw [avgR, hdiv]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

lemma integral_bumpUpper_le {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d) :
    ∫ z : 𝕋, (bumpFn ((a + b) / 2) ((b - a) / 2 + d) d) z ∂AddCircle.haarAddCircle
      ≤ (b - a) + 2 * d := by
  have h := integral_le_measure (G := bumpFn ((a + b) / 2) ((b - a) / 2 + d) d)
      (A := closedBall ((((a + b) / 2 : ℝ)) : 𝕋) ((b - a) / 2 + d))
      measurableSet_closedBall ?_ (fun z => bumpFn_le_one _ _ _ _)
  · rw [haar_closedBall] at h
    refine h.trans ?_
    rw [max_le_iff]
    exact ⟨(min_le_right _ _).trans (by linarith), by linarith⟩
  · intro z hz
    refine bumpFn_eq_zero hd ?_
    rw [mem_closedBall, dist_eq_norm] at hz
    push_neg at hz
    exact hz.le

lemma le_integral_bumpLower {a b d : ℝ} (hb1 : b - a ≤ 1) (hd : 0 < d) :
    (b - a) - 2 * d
      ≤ ∫ z : 𝕋, (bumpFn ((a + b) / 2) ((b - a) / 2) d) z ∂AddCircle.haarAddCircle := by
  have h := measure_le_integral (G := bumpFn ((a + b) / 2) ((b - a) / 2) d)
      (A := closedBall ((((a + b) / 2 : ℝ)) : 𝕋) ((b - a) / 2 - d))
      measurableSet_closedBall ?_ (fun z => bumpFn_nonneg _ _ _ _)
  · rw [haar_closedBall] at h
    refine le_trans ?_ h
    have hmin : min 1 (2 * ((b - a) / 2 - d)) = 2 * ((b - a) / 2 - d) :=
      min_eq_right (by linarith)
    calc (b - a) - 2 * d = min 1 (2 * ((b - a) / 2 - d)) := by rw [hmin]; ring
      _ ≤ max (min 1 (2 * ((b - a) / 2 - d))) 0 := le_max_left _ _
  · intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    exact le_of_eq (bumpFn_eq_one hd hz).symm

/-! ### Main theorem -/

/-- **Weyl's equidistribution criterion.**  If all nontrivial exponential sums of a real
sequence `x` are asymptotically negligible, then `x` is equidistributed modulo one: for every
subinterval `[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms whose fractional part lies
in `[a, b)` converges to the length `b - a`. -/
theorem equidistribution_of_asymptotic (x : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * x n)) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd : (0 : ℝ) < ε / 8 := by linarith
  have hupTend := avgR_tendsto x hW (bumpFn ((a + b) / 2) ((b - a) / 2 + ε / 8) (ε / 8))
  have hlowTend := avgR_tendsto x hW (bumpFn ((a + b) / 2) ((b - a) / 2) (ε / 8))
  rw [Metric.tendsto_atTop] at hupTend hlowTend
  obtain ⟨N₁, hN₁⟩ := hupTend (ε / 8) hd
  obtain ⟨N₂, hN₂⟩ := hlowTend (ε / 8) hd
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_of_max_le_left hN)
  have h2 := hN₂ N (le_of_max_le_right hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hIu := integral_bumpUpper_le (a := a) (b := b) hab hd
  have hIl := le_integral_bumpLower (a := a) (b := b) (by linarith) hd
  have hlow := avgR_bumpLower_le x (a := a) (b := b) (d := ε / 8) ha hb hd N
  have hup := le_avgR_bumpUpper x (a := a) (b := b) (d := ε / 8) hd N
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Application: irrational rotations

This section shows that the hypothesis of `equidistribution_of_asymptotic` is satisfiable, and
recovers the classical three-line consequence: the sequence `n ↦ n • α` is equidistributed
modulo one for every irrational `α`. -/

lemma weyl_sum_irrational {α : ℝ} (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ))) atTop (𝓝 0) := by
  set w : ℝ := 2 * π * k * α with hw
  set z : ℂ := Complex.exp (w * Complex.I) with hz
  have hznorm : ‖z‖ = 1 := by rw [hz]; exact Complex.norm_exp_ofReal_mul_I w
  have hzne : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hm' : (w : ℂ) * Complex.I = ((m : ℂ) * (2 * π)) * Complex.I := by rw [hm]; ring
    have hw2 : (w : ℂ) = (m : ℂ) * (2 * π) := mul_right_cancel₀ Complex.I_ne_zero hm'
    have hwr : w = (m : ℝ) * (2 * π) := by exact_mod_cast hw2
    have h2π : (2 * π : ℝ) ≠ 0 := by positivity
    have hka : (2 * π) * ((k : ℝ) * α) = (2 * π) * (m : ℝ) := by
      rw [hw] at hwr; ring_nf; ring_nf at hwr; linarith
    exact (Irrational.intCast_mul hα hk).ne_int m (mul_left_cancel₀ h2π hka)
  have hterm : ∀ n : ℕ,
      Complex.exp (2 * π * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ)) = z ^ n := by
    intro n
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    rw [hw]
    push_cast
    ring
  have hzpos : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero_of_ne hzne
  have hsum : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    intro N
    rw [geom_sum_eq hzne N, norm_div]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, hznorm, one_pow, norm_one]
      norm_num
    gcongr
  have hbound : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ))‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    simp only [hterm]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hrw : (2 / ‖z - 1‖) / (N : ℝ) = (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (hsum N) (by positivity)
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- **Equidistribution of irrational rotations.**  For irrational `α`, the fractional parts of
`n * α` are equidistributed in `[0, 1)`. -/
theorem equidistribution_irrational_rotation {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * α) ∈ Set.Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a)) :=
  equidistribution_of_asymptotic (fun n : ℕ => (n : ℝ) * α)
    (fun k hk => weyl_sum_irrational hα k hk) ha hab hb

end Brockian.Equidistribution

