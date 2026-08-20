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

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix cosine of a complex square matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/

theorem CosTraceNorm3499_sharp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖(Fintype.card n : ℂ) - (cosMat A).trace‖ ≤ ((A * A).trace.re) / 2 := by
  set lam : n → ℝ := hA.eigenvalues with hlam
  have htr : (cosMat A).trace = ((∑ i, Real.cos (lam i) : ℝ) : ℂ) := by
    rw [trace_cosMat_eq hA]; push_cast; rfl
  have hAA : (A * A).trace = ((∑ i, (lam i) ^ 2 : ℝ) : ℂ) := by
    rw [trace_mul_self_eq hA]; push_cast; rfl
  have hAAre : (A * A).trace.re = ∑ i, (lam i) ^ 2 := by
    rw [hAA, Complex.ofReal_re]
  have hdiff : (Fintype.card n : ℂ) - (cosMat A).trace
      = (((Fintype.card n : ℝ) - ∑ i, Real.cos (lam i) : ℝ) : ℂ) := by
    rw [htr]; push_cast; ring
  rw [hdiff, hAAre, Complex.norm_real, Real.norm_eq_abs]
  have hcard : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp [Finset.card_univ]
  have hupper : (Fintype.card n : ℝ) - ∑ i, Real.cos (lam i) ≤ (∑ i, (lam i) ^ 2) / 2 := by
    rw [hcard, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Real.one_sub_sq_div_two_le_cos (x := lam i)
    linarith
  have hlower : 0 ≤ (Fintype.card n : ℝ) - ∑ i, Real.cos (lam i) := by
    rw [hcard, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := Real.cos_le_one (lam i); linarith
  rw [abs_of_nonneg hlower]
  exact hupper

end Brockian

