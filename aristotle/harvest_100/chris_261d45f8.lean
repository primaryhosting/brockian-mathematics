import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real Complex
open scoped FourierTransform

/-! ### The triangular (tent) function and its Fourier transform -/

/-- The tent function `t ↦ max (1 - |t|) 0`, real valued. -/
noncomputable def tentR (t : ℝ) : ℝ := max (1 - |t|) 0

/-- The tent function, complex valued. -/
noncomputable def tent (t : ℝ) : ℂ := (tentR t : ℂ)

/-- The character `v ↦ exp (-i c v)`. -/
noncomputable def ee (c v : ℝ) : ℂ := Complex.exp ((-(c * v) : ℝ) * I)

/-- An antiderivative of `v ↦ ee c v * (a + b v)` for `c ≠ 0`. -/
noncomputable def antid (c a b : ℝ) (u : ℝ) : ℂ :=
  ((a + b * u : ℝ) : ℂ) * ee c u / (-(c * I)) + (b : ℂ) * ee c u / (c : ℂ) ^ 2

lemma continuous_tentR : Continuous tentR := by unfold tentR; fun_prop

lemma continuous_tent : Continuous tent := by unfold tent tentR; fun_prop

lemma continuous_ee (c : ℝ) : Continuous (ee c) := by unfold ee; fun_prop

lemma tentR_eq_zero {t : ℝ} (h : 1 ≤ |t|) : tentR t = 0 := by
  simp [tentR, sub_nonpos.2 h]

lemma hasCompactSupport_tent : HasCompactSupport tent := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tent, tentR_eq_zero this]

lemma integrable_tent : MeasureTheory.Integrable tent :=
  continuous_tent.integrable_of_hasCompactSupport hasCompactSupport_tent

lemma hasDerivAt_ee (c v : ℝ) : HasDerivAt (fun u : ℝ => ee c u) (-(c * I) * ee c v) v := by
  have h0 : HasDerivAt (fun u : ℝ => (-(c * u) : ℝ)) (-c) v := by
    simpa using ((hasDerivAt_id v).const_mul (-c))
  have h : HasDerivAt (fun u : ℝ => ((-(c * u) : ℝ) : ℂ) * I) (-(c * I)) v := by
    simpa [mul_comm] using (h0.ofReal_comp.mul_const I)
  simpa [ee, mul_comm] using h.cexp

lemma hasDerivAt_antid (c : ℝ) (hc : c ≠ 0) (a b : ℝ) (v : ℝ) :
    HasDerivAt (antid c a b) (ee c v * ((a + b * v : ℝ) : ℂ)) v := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have he := hasDerivAt_ee c v
  have hlin : HasDerivAt (fun u : ℝ => ((a + b * u : ℝ) : ℂ)) (b : ℂ) v := by
    have h : HasDerivAt (fun u : ℝ => (a + b * u : ℝ)) b v := by
      simpa using ((hasDerivAt_id v).const_mul b).const_add a
    simpa using h.ofReal_comp
  have h1 := ((hlin.mul he).div_const (-(c * I))).add ((he.const_mul (b : ℂ)).div_const ((c : ℂ) ^ 2))
  convert h1 using 1
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  ring_nf
  rw [hI]
  ring

lemma integral_piece (c : ℝ) (hc : c ≠ 0) (a b x y : ℝ) :
    ∫ v in x..y, ee c v * ((a + b * v : ℝ) : ℂ) = antid c a b y - antid c a b x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_antid c hc a b v)
  exact Continuous.intervalIntegrable ((continuous_ee c).mul (by fun_prop)) _ _

lemma sum_ee (c : ℝ) : ee c (-1) + ee c 1 = 2 * Complex.cos (c : ℂ) := by
  have h1 : ee c (-1) = Complex.exp ((c : ℂ) * I) := by rw [ee]; norm_num
  have h2 : ee c 1 = Complex.exp ((-c : ℂ) * I) := by rw [ee]; norm_num
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The (complexified) tent integral, for a nonzero frequency. -/
lemma integral_tent_ne (c : ℝ) (hc : c ≠ 0) :
    ∫ v in (-1 : ℝ)..1, ee c v * tent v = (((2 - 2 * Real.cos c) / c ^ 2 : ℝ) : ℂ) := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun v => ee c v * tent v) volume x y :=
    fun x y => Continuous.intervalIntegrable ((continuous_ee c).mul continuous_tent) x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ)) (hint (-1) 0) (hint 0 1)]
  have e1 : ∫ v in (-1 : ℝ)..0, ee c v * tent v
      = ∫ v in (-1 : ℝ)..0, ee c v * ((1 + 1 * v : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    have h : |v| = -v := abs_of_nonpos hv.2
    simp only [tent, tentR, h]
    norm_num
    left
    rw [max_eq_left (by linarith [hv.1])]
    push_cast
    ring
  have e2 : ∫ v in (0 : ℝ)..1, ee c v * tent v
      = ∫ v in (0 : ℝ)..1, ee c v * ((1 + (-1) * v : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have h : |v| = v := abs_of_nonneg hv.1
    simp only [tent, tentR, h]
    norm_num
    left
    rw [max_eq_left (by linarith [hv.2])]
    push_cast
    ring
  rw [e1, e2, integral_piece c hc, integral_piece c hc]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hee0 : ee c 0 = 1 := by simp [ee]
  simp only [antid, hee0]
  have hs := sum_ee c
  push_cast
  field_simp
  linear_combination (-I) * hs

/-- The tent integral at frequency zero. -/
lemma integral_tentR_zero : ∫ v in (-1 : ℝ)..1, tentR v = 1 := by
  have h : ∫ v in (-1 : ℝ)..1, tentR v
      = (∫ v in (-1 : ℝ)..0, (1 + v)) + ∫ v in (0 : ℝ)..1, (1 - v) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (Continuous.intervalIntegrable continuous_tentR _ _)
      (Continuous.intervalIntegrable continuous_tentR _ _)]
    congr 1
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
      simp only [tentR, abs_of_nonpos hv.2]
      rw [max_eq_left (by linarith [hv.1])]
      ring
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      simp only [tentR, abs_of_nonneg hv.1]
      rw [max_eq_left (by linarith [hv.2])]
  rw [h, intervalIntegral.integral_add _root_.intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_sub _root_.intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
  norm_num [integral_id]

lemma fourier_tent_eq_intervalIntegral (w : ℝ) :
    𝓕 tent w = ∫ v in (-1 : ℝ)..1, ee (2 * π * w) v * tent v := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    rw [smul_eq_mul, ee, show (2 * π * w * v : ℝ) = 2 * π * v * w from by ring]
    norm_num
  · intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    have : 1 ≤ |v| := by
      rcases hv with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tent, tentR_eq_zero this]

/-- The Fourier transform of the tent function is `sinc (π w) ^ 2`. -/
lemma fourier_tent (w : ℝ) : 𝓕 tent w = (((Real.sinc (π * w)) ^ 2 : ℝ) : ℂ) := by
  rw [fourier_tent_eq_intervalIntegral]
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : ∀ v : ℝ, ee (2 * π * 0) v * tent v = ((tentR v : ℝ) : ℂ) := by
      intro v; simp [ee, tent]
    simp only [h0]
    rw [intervalIntegral.integral_ofReal, integral_tentR_zero]
    norm_num
  · have hc : 2 * π * w ≠ 0 := by
      have := Real.pi_ne_zero
      simp [hw, this]
    rw [integral_tent_ne _ hc]
    congr 1
    have hpw : π * w ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
    rw [Real.sinc_of_ne_zero hpw]
    have hcos : Real.cos (2 * π * w) = 1 - 2 * Real.sin (π * w) ^ 2 := by
      rw [show (2 * π * w : ℝ) = 2 * (π * w) from by ring, Real.cos_two_mul']
      have := Real.sin_sq_add_cos_sq (π * w)
      nlinarith [this]
    rw [hcos]
    field_simp
    ring

/-! ### Integrability of `sinc ^ 2` -/

lemma sinc_mul_self (x : ℝ) : Real.sinc x * x = Real.sin x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

lemma sinc_sq_le (x : ℝ) : (Real.sinc x) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 : (Real.sinc x) ^ 2 ≤ 1 := by
    have h := Real.abs_sinc_le_one x
    nlinarith [abs_nonneg (Real.sinc x), sq_abs (Real.sinc x)]
  have h2 : (Real.sinc x) ^ 2 * x ^ 2 = (Real.sin x) ^ 2 := by
    rw [← mul_pow, sinc_mul_self]
  have h3 : (Real.sin x) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_le_one x, Real.neg_one_le_sin x]
  rw [show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) from by ring, le_div_iff₀ hpos]
  nlinarith

lemma integrable_sinc_sq : MeasureTheory.Integrable (fun x : ℝ => (Real.sinc x) ^ 2) := by
  apply MeasureTheory.Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2)
  · exact (Real.continuous_sinc.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_sq_le x

lemma integrable_fourier_tent : MeasureTheory.Integrable (𝓕 tent) := by
  have h : (𝓕 tent) = fun w : ℝ => (((Real.sinc (π * w)) ^ 2 : ℝ) : ℂ) := funext fourier_tent
  rw [h]
  exact (integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero).ofReal

/-! ### The main computation -/

lemma integral_sinc_pi_mul_sq : ∫ w : ℝ, (Real.sinc (π * w)) ^ 2 = 1 := by
  have hinv := integrable_tent.fourierInv_fourier_eq integrable_fourier_tent
    (v := (0 : ℝ)) continuous_tent.continuousAt
  rw [Real.fourierInv_eq] at hinv
  have h1 : ∫ v : ℝ, 𝓕 tent v = (1 : ℂ) := by
    have : ∫ v : ℝ, 𝓕 tent v = tent 0 := by simpa using hinv
    rw [this]
    simp [tent, tentR]
  have h2 : ∫ v : ℝ, (((Real.sinc (π * v)) ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h1]
    exact MeasureTheory.integral_congr_ae (by filter_upwards with v using (fourier_tent v).symm)
  rw [show (fun v : ℝ => (((Real.sinc (π * v)) ^ 2 : ℝ) : ℂ))
        = fun v => Complex.ofRealCLM ((Real.sinc (π * v)) ^ 2) from rfl,
    ContinuousLinearMap.integral_comp_comm _ (integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero),
    Complex.ofRealCLM_apply] at h2
  exact_mod_cast h2

lemma integral_sinc_sq' : ∫ x : ℝ, (Real.sinc x) ^ 2 = π := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun x : ℝ => (Real.sinc x) ^ 2) π
  rw [integral_sinc_pi_mul_sq] at h
  rw [smul_eq_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹)] at h
  field_simp at h
  linarith [h]

/-- **The normalization integral of the sine kernel**:
`∫ x : ℝ, (sin x / x) ^ 2 dx = π`.  (At `x = 0` the integrand is `0` in Lean, which does not
affect the value of the integral since `{0}` is a null set; the integrand agrees a.e. with the
continuous function `sinc ^ 2`.) -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  rw [← integral_sinc_sq']
  apply MeasureTheory.integral_congr_ae
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h0] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

