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

theorem abs_cosTrace_le_pi_div_abs (n : ℕ) (t : ℝ) (ht0 : t ≠ 0) (ht : |t| ≤ Real.pi) :
    |cosTrace n t| ≤ Real.pi / |t| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlow : |t| / Real.pi ≤ |Real.sin (t / 2)| := abs_div_pi_le_abs_sin_half ht
  have hspos : 0 < |Real.sin (t / 2)| := lt_of_lt_of_le (by positivity) hlow
  have hs : Real.sin (t / 2) ≠ 0 := by
    intro h; rw [h] at hspos; simp at hspos
  refine (abs_cosTrace_le_inv_abs_sin n t hs).trans ?_
  calc 1 / |Real.sin (t / 2)| ≤ 1 / (|t| / Real.pi) :=
        one_div_le_one_div_of_le (by positivity) hlow
    _ = Real.pi / |t| := one_div_div _ _

end Brockian

