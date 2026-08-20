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

theorem norm_expSum (n : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    ‖expSum n t‖ = dirichletTraceNorm n t := by
  set z : ℂ := Complex.exp ((t : ℂ) * Complex.I) with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    have := norm_exp_mul_I_sub_one t
    rw [← hzdef, h] at this
    simp at this
    exact ht (by simpa using this)
  have hgeom : expSum n t = ∑ k ∈ Finset.range n, z ^ k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzn : z ^ n = Complex.exp (((n * t : ℝ) : ℂ) * Complex.I) := by
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hgeom, geom_sum_eq hz1, norm_div, hzn, norm_exp_mul_I_sub_one, norm_exp_mul_I_sub_one,
    dirichletTraceNorm]
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- Pythagoras for the cosine and sine traces. -/
