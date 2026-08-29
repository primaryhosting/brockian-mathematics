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


theorem harmonicOscillatorPMap_dense :
    Dense (harmonicOscillatorPMap.domain : Set L2R) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → L2R)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f
    rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [harmonicOscillatorPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

end Brockian.Weyl.HarmonicOscillator

/-
  RequestProject/GaussianSchwartz.lean

  The Gaussian `x ↦ exp (-x²/2)` as an element of the complex Schwartz space
  `𝓢(ℝ, ℂ)`.  All its derivatives are Hermite polynomials times the Gaussian
  (`Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`), and every polynomial
  times the Gaussian is bounded, which is exactly the Schwartz decay condition.
-/
import Mathlib

open Real Nat Polynomial SchwartzMap

namespace Brockian.Gaussian

/-- `|x|^m e^{-x²/2}` is bounded by `m! 2^m + 1`. -/
