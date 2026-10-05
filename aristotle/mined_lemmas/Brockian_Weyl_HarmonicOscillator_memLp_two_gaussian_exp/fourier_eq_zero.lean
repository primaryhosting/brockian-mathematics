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


theorem fourier_eq_zero (ξ : ℝ) : 𝓕 G ξ = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) • G v
      = Complex.exp (((-2 * π * ξ : ℝ) * Complex.I) * v) * G v := by
    intro v
    congr 2
    push_cast
    ring
  simp_rw [this]
  exact integral_cexp_mul_eq_zero hmeas hint hmom _

/-- **Moment theorem.** A function with uniform exponential integrability whose
moments `∫ xⁿ G x` all vanish is zero almost everywhere. -/
