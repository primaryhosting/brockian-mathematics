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


theorem harmonicOscillatorPMap_essentiallySelfAdjoint :
    EssentiallySelfAdjoint harmonicOscillatorPMap :=
  ⟨harmonicOscillator_deficiency_eq_bot (by rw [Complex.I_im]; exact one_ne_zero),
   harmonicOscillator_deficiency_eq_bot (by simp [Complex.neg_im, Complex.I_im])⟩

end Brockian.Weyl.HarmonicOscillator

/-
  RequestProject/Hermite.lean

  Hermite functions for the Schwartz-core harmonic oscillator
  `oscillatorSchwartz f = -f'' + x² f`.

  We use the creation operator `A† f = x f - f'`, which maps the Schwartz space
  to itself.  Starting from the Gaussian `h₀ = e^{-x²/2}` (an eigenfunction with
  eigenvalue `1`), the functions `hermiteFun n = (A†)ⁿ h₀` are eigenfunctions with
  eigenvalue `2n+1`, and their span contains every `x ↦ xⁿ e^{-x²/2}`.
-/
import RequestProject.Corpus
import RequestProject.GaussianSchwartz

open SchwartzMap Brockian.Gaussian

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.SchrodingerMinimal

/-! ### Multiplication by `x` and the creation operator -/

