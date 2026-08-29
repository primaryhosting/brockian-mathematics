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


theorem inner_schwartzToL2 (g : L2R) (f : SchwartzMap ℝ ℂ) :
    ⟪g, schwartzToL2 f⟫_ℂ = ∫ x : ℝ, (starRingEnd ℂ) (g x) * f x := by
  rw [schwartzToL2_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure ℝ)] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-- **Both deficiency spaces of the harmonic-oscillator core are trivial.**
For any non-real `z`, `ker (T* - z) = ⊥`. -/
