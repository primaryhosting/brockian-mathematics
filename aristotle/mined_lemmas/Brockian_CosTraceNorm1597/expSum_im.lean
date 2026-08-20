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

theorem expSum_im (n : ℕ) (t : ℝ) : (expSum n t).im = sinTrace n t := by
  rw [expSum, Complex.im_sum, sinTrace]
  exact Finset.sum_congr rfl (fun k _ => Complex.exp_ofReal_mul_I_im _)

/-! ## The trace norm -/

/-- The modulus of the exponential sum is the Dirichlet trace norm. -/
