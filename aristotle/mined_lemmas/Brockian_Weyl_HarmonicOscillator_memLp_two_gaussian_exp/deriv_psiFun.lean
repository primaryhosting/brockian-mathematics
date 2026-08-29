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


theorem deriv_psiFun (n : ℕ) (x : ℝ) :
    deriv ((psiFun n : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = (n : ℂ) * (x : ℂ) ^ (n - 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ)
        - (x : ℂ) ^ (n + 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
  have hfun : ((psiFun n : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => (y : ℂ) ^ n * (Real.exp (-(y ^ 2 / 2)) : ℂ) := funext (psiFun_apply n)
  rw [hfun]
  have hd : HasDerivAt (fun y : ℝ => (y : ℂ) ^ n * (Real.exp (-(y ^ 2 / 2)) : ℂ))
      (((n : ℂ) * (x : ℂ) ^ (n - 1) * 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ)
        + (x : ℂ) ^ n * (-(x : ℂ) * (Real.exp (-(x ^ 2 / 2)) : ℂ))) x :=
    ((hasDerivAt_ofReal x).pow n).mul (hasDerivAt_cgauss x)
  rw [hd.deriv]
  ring

/-- The creation operator on the monomial family:
`A† (xⁿ e^{-x²/2}) = 2 xⁿ⁺¹ e^{-x²/2} - n xⁿ⁻¹ e^{-x²/2}`. -/
