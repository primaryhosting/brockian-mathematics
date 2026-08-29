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


theorem memLp_two_gaussian_exp (c : ℝ) :
    MemLp (fun x : ℝ => Real.exp (-(x ^ 2 / 2) + c * |x|)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (-(x ^ 2 / 2) + c * |x|))
      (volume : Measure ℝ) := by fun_prop
  rw [memLp_two_iff_integrable_sq hmeas]
  have hb : Integrable (fun x : ℝ => Real.exp (2 * c ^ 2) * Real.exp (-(1 / 2) * x ^ 2))
      (volume : Measure ℝ) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  refine Integrable.mono' hb (by fun_prop) ?_
  filter_upwards with x
  have hx : -(x ^ 2) + 2 * c * |x| ≤ 2 * c ^ 2 + -(1 / 2) * x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 2 * c), sq_abs x, abs_nonneg x]
  have h1 : (Real.exp (-(x ^ 2 / 2) + c * |x|)) ^ 2
      = Real.exp (-(x ^ 2) + 2 * c * |x|) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), h1, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hx

