import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-! # The `CosTraceNorm` family

For an angle `t` and `n : ℕ` we study the truncated cosine trace
`cosTrace n t = ∑_{k < n} cos (k t)`, which is (half) the trace of the geometric sum
`∑_{k < n} R(t)^k` of powers of the planar rotation matrix `R(t)`.

The corresponding "trace norm" is the Schatten-1 norm of that operator, which for
these normal `2 × 2` matrices equals `2 * ‖∑_{k<n} e^{ikt}‖`, i.e. twice the
Dirichlet quotient `|sin (n t / 2)| / |sin (t / 2)|`.

The main result `Brockian.CosTraceNorm1597` bounds `|cosTrace n t|` by the minimum of
the trivial bound `n` and the Dirichlet trace norm.
-/

/-- The truncated cosine trace `∑_{k<n} cos (k t)`. -/

theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul' (θ / 2)
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    have e : (2 : ℝ) * (θ / 2) = θ := by ring
    rw [e] at h; nlinarith
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    have e : (2 : ℝ) * (θ / 2) = θ := by ring
    rw [e] at h; linarith
  have hrhs : 2 * |Real.sin (θ / 2)| = Real.sqrt (4 * Real.sin (θ / 2) ^ 2) := by
    rw [show (4 : ℝ) * Real.sin (θ / 2) ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 from by
      rw [mul_pow, sq_abs]; ring]
    exact (Real.sqrt_sq (by positivity)).symm
  rw [Complex.exp_mul_I, Complex.norm_def, Complex.normSq_apply, hrhs]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    hc, hs]
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

