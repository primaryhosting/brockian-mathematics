/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` to precede any
-- module docstring; the identical header is repeated as the module docstring below.)

import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder

namespace Brockian

/-- The trace norm (Schatten 1-norm) of a complex square matrix `A`:
the trace of the positive semidefinite square root of `Aᴴ * A`,
i.e. the sum of the singular values of `A`. -/
noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (Aᴴ * A)).trace.re

/-- If the columns of `A` are orthonormal (`Aᴴ * A = 1`), then all singular values of `A`
equal `1`, so the trace norm is the size of the matrix. -/
theorem traceNorm_of_conjTranspose_mul_self_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : Aᴴ * A = 1) : traceNorm A = Fintype.card n := by
  unfold traceNorm
  rw [h, CFC.sqrt_one]
  simp

/-- If `Aᴴ * A = 1` then every diagonal entry of `A` has norm at most `1`. -/
theorem norm_diag_le_one_of_conjTranspose_mul_self_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : Aᴴ * A = 1) (i : n) : ‖A i i‖ ≤ 1 := by
  have h1 : ∑ k, ‖A k i‖ ^ 2 = 1 := by
    have hd := congrArg (fun M => M i i) h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hd
    have h2 : ((∑ k, ‖A k i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      rw [← hd]
      refine Finset.sum_congr rfl fun k _ => ?_
      simpa [mul_comm] using (Complex.mul_conj' (A k i)).symm
    exact_mod_cast h2
  have hle := Finset.single_le_sum (f := fun k => ‖A k i‖ ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ i)
  rw [h1] at hle
  nlinarith [norm_nonneg (A i i)]

/-- The trace-norm bound `|tr A| ≤ ‖A‖₁` for matrices with orthonormal columns. -/
theorem norm_trace_le_traceNorm_of_conjTranspose_mul_self_eq_one {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (h : Aᴴ * A = 1) : ‖A.trace‖ ≤ traceNorm A := by
  rw [traceNorm_of_conjTranspose_mul_self_eq_one A h, Matrix.trace]
  calc ‖∑ i, A.diag i‖ ≤ ∑ i, ‖A.diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => norm_diag_le_one_of_conjTranspose_mul_self_eq_one A h i
    _ = Fintype.card n := by simp

/-- The `2 × 2` rotation matrix by angle `θ`, viewed as a complex matrix. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- Rotation matrices are unitary: `R(θ)ᴴ * R(θ) = 1`. -/
theorem rot_conjTranspose_mul_self (θ : ℝ) : (rot θ)ᴴ * (rot θ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The trace of `R(θ)` is `2 cos θ`. -/
theorem rot_trace (θ : ℝ) : (rot θ).trace = 2 * (Real.cos θ : ℂ) := by
  simp [rot, Matrix.trace, Fin.sum_univ_succ]
  ring

/--
**Cos Trace Norm 2707.**
For every angle `θ`, the `2 × 2` rotation matrix `R(θ)` has trace norm `2`,
its trace has norm `2 |cos θ|`, and consequently the trace-norm bound
`|tr R(θ)| ≤ ‖R(θ)‖₁` holds, i.e. `2 |cos θ| ≤ 2`.
-/
theorem CosTraceNorm2707 (θ : ℝ) :
    traceNorm (rot θ) = 2 ∧ ‖(rot θ).trace‖ = 2 * |Real.cos θ| ∧
      ‖(rot θ).trace‖ ≤ traceNorm (rot θ) := by
  have hU := rot_conjTranspose_mul_self θ
  have h1 : traceNorm (rot θ) = 2 := by
    rw [traceNorm_of_conjTranspose_mul_self_eq_one _ hU]
    simp
  refine ⟨h1, ?_, norm_trace_le_traceNorm_of_conjTranspose_mul_self_eq_one _ hU⟩
  rw [rot_trace, norm_mul, Complex.norm_real]
  norm_num

end Brockian

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

