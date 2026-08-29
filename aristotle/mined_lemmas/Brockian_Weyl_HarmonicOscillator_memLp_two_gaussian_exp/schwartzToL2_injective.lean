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


theorem schwartzToL2_injective : Function.Injective schwartzToL2 := by
  intro f g hfg
  have hf := f.coeFn_toLp 2 (volume : Measure ℝ)
  have hg := g.coeFn_toLp 2 (volume : Measure ℝ)
  have hae : (f : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ) := by
    have : (f.toLp 2 (volume : Measure ℝ) : ℝ → ℂ) =ᵐ[volume]
        (g.toLp 2 (volume : Measure ℝ) : ℝ → ℂ) := by
      rw [show f.toLp 2 (volume : Measure ℝ) = g.toLp 2 (volume : Measure ℝ) from hfg]
    filter_upwards [hf, hg, this] with x hx hy hz
    rw [← hx, ← hy, hz]
  exact SchwartzMap.ext
    (congrFun ((f.continuous.ae_eq_iff_eq (volume : Measure ℝ) g.continuous).mp hae))

/-- The second derivative on the Schwartz core. -/
