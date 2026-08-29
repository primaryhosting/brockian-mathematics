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


theorem integrable_pow_mul (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * G x) volume := by
  refine Integrable.mono' (((hint 1).const_mul (n ! : ℝ))) ?_ ?_
  · exact (Complex.continuous_ofReal.aestronglyMeasurable.pow n).mul hmeas
  · filter_upwards with x
    have hpow : |x| ^ n ≤ (n ! : ℝ) * Real.exp |x| := by
      have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
      have hn : (0 : ℝ) < (n ! : ℝ) := by positivity
      rw [div_le_iff₀ hn] at h
      linarith
    have hG : (0 : ℝ) ≤ ‖G x‖ := norm_nonneg _
    calc ‖(x : ℂ) ^ n * G x‖ = |x| ^ n * ‖G x‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ((n ! : ℝ) * Real.exp |x|) * ‖G x‖ := by gcongr
      _ = (n ! : ℝ) * (‖G x‖ * Real.exp (1 * |x|)) := by rw [one_mul]; ring

variable (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * G x = 0)

include hmom

/-- The exponential integral `∫ exp (w x) G x` vanishes for every complex `w`:
expand the exponential in its power series and use the vanishing moments. -/
