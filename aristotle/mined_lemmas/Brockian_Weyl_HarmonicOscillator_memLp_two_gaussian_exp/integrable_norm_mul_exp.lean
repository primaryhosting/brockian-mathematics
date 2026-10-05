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


theorem integrable_norm_mul_exp (g : Lp ℂ 2 (volume : Measure ℝ)) (c : ℝ) :
    Integrable (fun x : ℝ =>
      ‖(starRingEnd ℂ) (g x) * (Real.exp (-(x ^ 2 / 2)) : ℂ)‖ * Real.exp (c * |x|))
      (volume : Measure ℝ) := by
  have hfun : (fun x : ℝ =>
        ‖(starRingEnd ℂ) (g x) * (Real.exp (-(x ^ 2 / 2)) : ℂ)‖ * Real.exp (c * |x|))
      = (fun x : ℝ => ‖g x‖) * (fun x : ℝ => Real.exp (-(x ^ 2 / 2) + c * |x|)) := by
    funext x
    have h1 : ‖(starRingEnd ℂ) (g x) * (Real.exp (-(x ^ 2 / 2)) : ℂ)‖
        = ‖g x‖ * Real.exp (-(x ^ 2 / 2)) := by
      rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos _).le]
    rw [h1, Pi.mul_apply, Real.exp_add]
    ring
  rw [hfun]
  exact MemLp.integrable_mul (Lp.memLp g).norm (memLp_two_gaussian_exp c)

/-! ### The deficiency spaces are trivial -/

/-- The inner product of an `L²` function against an embedded Schwartz function
is the corresponding integral. -/
