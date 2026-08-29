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


theorem oscillator_creation (f : SchwartzMap ℝ ℂ) :
    oscillatorSchwartz (creationSchwartz f)
      = creationSchwartz (oscillatorSchwartz f) + (2 : ℂ) • creationSchwartz f := by
  ext x
  set f1 : ℝ → ℂ := deriv (f : ℝ → ℂ) with hf1
  set f2 : ℝ → ℂ := deriv f1 with hf2
  set f3 : ℝ → ℂ := deriv f2 with hf3
  have hd1 : HasDerivAt (f : ℝ → ℂ) (f1 x) x := schwartz_hasDerivAt f x
  have hd2 : HasDerivAt f1 (f2 x) x := by
    have h := schwartz_hasDerivAt (SchwartzMap.derivCLM ℂ ℂ f) x
    simp only [coe_derivCLM] at h
    exact h
  have hd3 : HasDerivAt f2 (f3 x) x := by
    have h := schwartz_hasDerivAt (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) x
    simp only [coe_derivCLM] at h
    exact h
  have hB : deriv (deriv ((creationSchwartz f : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x
      = f1 x + (f1 x + (x : ℂ) * f2 x) - f3 x := by
    rw [deriv_creation]
    exact ((hd1.add (by simpa using (hasDerivAt_ofReal x).mul hd2)).sub hd3).deriv
  have hC : deriv ((oscillatorSchwartz f : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = -f3 x + (2 * (x : ℂ) * f x + (x : ℂ) ^ 2 * f1 x) := by
    rw [coe_oscillator]
    exact (hd3.neg.add (by simpa using ((hasDerivAt_ofReal x).pow 2).mul hd1)).deriv
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, oscillatorSchwartz_apply,
    creationSchwartz_apply, hB, hC, smul_eq_mul, ← hf1, ← hf2]
  ring

/-! ### The Gaussian is an eigenfunction -/

