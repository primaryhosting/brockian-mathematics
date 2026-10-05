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


noncomputable def gaussianSchwartz : SchwartzMap ℝ ℂ where
  toFun := fun x => (Real.exp (-(x ^ 2 / 2)) : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) by fun_prop)
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := poly_gauss_bounded ((hermite n).map (Int.castRingHom ℝ)) k
    refine ⟨C, fun x => ?_⟩
    have hnorm : ‖iteratedFDeriv ℝ n (fun y : ℝ => ((gaussReal y : ℝ) : ℂ)) x‖
        = ‖iteratedDeriv n gaussReal x‖ := by
      have := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := gaussReal) (x := x)
        contDiff_gaussReal.contDiffAt (i := n) (by exact_mod_cast le_top)
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact this
    have hfun : (fun y : ℝ => ((Real.exp (-(y ^ 2 / 2)) : ℝ) : ℂ))
        = fun y : ℝ => ((gaussReal y : ℝ) : ℂ) := rfl
    rw [hfun, hnorm, iteratedDeriv_gaussReal]
    have hev : (aeval x (hermite n) : ℝ)
        = ((hermite n).map (Int.castRingHom ℝ)).eval x := by simp [aeval_def, eval_map]
    rw [hev]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Real.abs_exp]
    exact hC x

