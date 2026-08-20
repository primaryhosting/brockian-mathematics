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

theorem abs_div_pi_le_abs_sin_half {t : ℝ} (ht : |t| ≤ Real.pi) :
    |t| / Real.pi ≤ |Real.sin (t / 2)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨hl, hr⟩ := abs_le.mp ht
  have habs : |Real.sin (t / 2)| = Real.sin (|t| / 2) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    · have hn : 0 ≤ Real.sin (-(t / 2)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at hn
      rw [abs_of_nonpos (by linarith), abs_of_neg h, show -t / 2 = -(t / 2) by ring, Real.sin_neg]
  rw [habs]
  have h2 : 2 / Real.pi * (|t| / 2) ≤ Real.sin (|t| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  calc |t| / Real.pi = 2 / Real.pi * (|t| / 2) := by field_simp
    _ ≤ Real.sin (|t| / 2) := h2

/-- Jordan-type trace-norm bound: for `0 < |t| ≤ π` the cosine traces are bounded by `π / |t|`,
uniformly in `n`. -/
