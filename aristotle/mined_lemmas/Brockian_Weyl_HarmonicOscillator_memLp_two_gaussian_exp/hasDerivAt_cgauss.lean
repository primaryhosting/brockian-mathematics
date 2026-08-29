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


theorem hasDerivAt_cgauss (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.exp (-(y ^ 2 / 2)) : ℂ))
      (-(x : ℂ) * (Real.exp (-(x ^ 2 / 2)) : ℂ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    simpa using ((hasDerivAt_pow 2 x).div_const 2).neg
  have hr : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      ((-x) * Real.exp (-(x ^ 2 / 2))) x := by
    simpa [mul_comm] using h1.exp
  simpa using hr.ofReal_comp

