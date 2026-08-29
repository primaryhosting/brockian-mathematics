/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/


theorem integral_cexp_mul_eq_zero (w : ℂ) :
    ∫ x : ℝ, Complex.exp (w * x) * G x = 0 := by
  set F : ℕ → ℝ → ℂ := fun n x => (w ^ n / (n ! : ℂ)) * ((x : ℂ) ^ n * G x) with hFdef
  have hmeasF : ∀ n, AEStronglyMeasurable (F n) volume := fun n =>
    AEStronglyMeasurable.const_mul
      ((Complex.continuous_ofReal.aestronglyMeasurable.pow n).mul hmeas) _
  have hnorm : ∀ (n : ℕ) (x : ℝ), ‖F n x‖ = (‖w‖ * |x|) ^ n / (n ! : ℝ) * ‖G x‖ := by
    intro n x
    simp only [hFdef, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast, mul_pow]
    ring
  -- the pointwise sum of the norms
  have hsumnorm : ∀ x : ℝ, ∑' n : ℕ, ‖F n x‖ = Real.exp (‖w‖ * |x|) * ‖G x‖ := by
    intro x
    simp only [hnorm]
    rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummable : ∀ x : ℝ, Summable fun n : ℕ => ‖F n x‖ := by
    intro x
    simp only [hnorm]
    exact (Real.summable_pow_div_factorial (‖w‖ * |x|)).mul_right _
  -- finiteness of the sum of the `L¹` norms
  have hfin : ∑' n : ℕ, ∫⁻ x : ℝ, ‖F n x‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun n => (hmeasF n).enorm)]
    have hpt : ∀ x : ℝ, ∑' n : ℕ, ‖F n x‖ₑ
        = ENNReal.ofReal (‖G x‖ * Real.exp (‖w‖ * |x|)) := by
      intro x
      have : ∀ n : ℕ, ‖F n x‖ₑ = ENNReal.ofReal ‖F n x‖ := fun n => by
        rw [← ofReal_norm_eq_enorm]
      simp only [this]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hsummable x), hsumnorm x,
        mul_comm]
    rw [lintegral_congr hpt]
    have hI := (hint ‖w‖).hasFiniteIntegral
    have heq : ∀ x : ℝ, ‖‖G x‖ * Real.exp (‖w‖ * |x|)‖ₑ
        = ENNReal.ofReal (‖G x‖ * Real.exp (‖w‖ * |x|)) := by
      intro x
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖G x‖ * Real.exp (‖w‖ * |x|))]
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm] at hI
    rw [lintegral_congr heq] at hI
    exact hI.ne
  have hpt : ∀ x : ℝ, ∑' n : ℕ, F n x = Complex.exp (w * x) * G x := by
    intro x
    have hexp : Complex.exp (w * x) = ∑' n : ℕ, (w * (x : ℂ)) ^ n / (n ! : ℂ) := by
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    rw [hexp, ← tsum_mul_right]
    exact tsum_congr fun n => by simp only [hFdef, mul_pow]; ring
  calc ∫ x : ℝ, Complex.exp (w * x) * G x
      = ∫ x : ℝ, ∑' n : ℕ, F n x := by simp_rw [hpt]
    _ = ∑' n : ℕ, ∫ x : ℝ, F n x := integral_tsum hmeasF hfin
    _ = 0 := by
        have : ∀ n : ℕ, ∫ x : ℝ, F n x = 0 := by
          intro n
          simp only [hFdef]
          rw [MeasureTheory.integral_const_mul, hmom n, mul_zero]
        simp [this]

/-- The Fourier transform of `G` vanishes identically. -/
