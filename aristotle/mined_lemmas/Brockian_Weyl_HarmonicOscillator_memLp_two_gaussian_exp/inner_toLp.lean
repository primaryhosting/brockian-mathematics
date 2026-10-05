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


theorem inner_toLp (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 f) (schwartzToL2 g) = ∫ x : ℝ, conj (f x) * g x := by
  rw [schwartzToL2_apply, schwartzToL2_apply,
    SchwartzMap.inner_toL2_toL2_eq f g (volume : Measure ℝ)]
  simp only [RCLike.inner_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

end Brockian.Weyl.SchrodingerMinimal

/-! ## The harmonic oscillator on the Schwartz core
(`Brockian/WeylHarmonicOscillator.lean`, verbatim up to the confining-shape part). -/

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- Multiplication by `x^2` preserves Schwartz space. -/
