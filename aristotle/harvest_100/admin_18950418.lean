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

set_option grind.warning false

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The trace of `cfc f A`, for a Hermitian matrix `A`, is the sum of `f` over the
eigenvalues of `A`. -/
theorem trace_cfc_eq_sum_eigenvalues (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]
  simp [Matrix.trace_diagonal]

/-- For a Hermitian matrix, the trace of `A ^ 2` is the squared Frobenius norm of `A`. -/
theorem trace_sq_eq_sum_normSq (hA : A.IsHermitian) :
    (A ^ 2).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [pow_two, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : A j i = star (A i j) := by
    have := hA.apply j i
    simpa [Matrix.IsHermitian] using this.symm
  rw [h]
  push_cast
  exact Complex.mul_conj' (A i j)

/-- The functional calculus applied to `x ↦ x ^ 2` returns the square of the matrix. -/
theorem cfc_sq (hA : A.IsHermitian) : cfc (fun x : ℝ => x ^ 2) A = A ^ 2 := by
  have h : IsSelfAdjoint A := hA
  rw [cfc_pow (R := ℝ) (a := A) (f := fun x : ℝ => x) 2]
  congr 1
  simpa using cfc_id ℝ A

/-- The sum of the squares of the eigenvalues of a Hermitian matrix equals its squared
Frobenius norm. -/
theorem sum_sq_eigenvalues (hA : A.IsHermitian) :
    ∑ i, (hA.eigenvalues i) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := trace_cfc_eq_sum_eigenvalues hA (fun x : ℝ => x ^ 2)
  rw [cfc_sq hA, trace_sq_eq_sum_normSq hA] at h
  exact_mod_cast h.symm

/-- **A trace-norm bound for the matrix cosine.**

For a Hermitian complex matrix `A` of size `n`, the cosine `cos A`, defined by the continuous
functional calculus, has trace within `‖A‖_F ^ 2 / 2` of `n`, where `‖A‖_F ^ 2 = ∑ i j, ‖A i j‖ ^ 2`
is the squared Frobenius (Hilbert–Schmidt) norm of `A`. -/
theorem CosTraceNorm4001 (hA : A.IsHermitian) :
    ‖(cfc Real.cos A).trace - (Fintype.card n : ℂ)‖ ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) / 2 := by
  have htr := trace_cfc_eq_sum_eigenvalues hA Real.cos
  have hcast : (cfc Real.cos A).trace - (Fintype.card n : ℂ)
      = ((∑ i, Real.cos (hA.eigenvalues i) - (Fintype.card n : ℝ) : ℝ) : ℂ) := by
    rw [htr]; push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hupper : ∑ i, Real.cos (hA.eigenvalues i) - (Fintype.card n : ℝ) ≤ 0 := by
    have : ∑ i, Real.cos (hA.eigenvalues i) ≤ ∑ _i : n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => Real.cos_le_one _
    simpa using this
  have hlower : -((∑ i, ∑ j, ‖A i j‖ ^ 2) / 2)
      ≤ ∑ i, Real.cos (hA.eigenvalues i) - (Fintype.card n : ℝ) := by
    have hstep : ∑ i, (1 - (hA.eigenvalues i) ^ 2 / 2)
        ≤ ∑ i, Real.cos (hA.eigenvalues i) :=
      Finset.sum_le_sum fun i _ => Real.one_sub_sq_div_two_le_cos
    have hsplit : ∑ i, (1 - (hA.eigenvalues i) ^ 2 / 2)
        = (Fintype.card n : ℝ) - (∑ i, (hA.eigenvalues i) ^ 2) / 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      simp
    rw [hsplit, sum_sq_eigenvalues hA] at hstep
    linarith
  refine ⟨hlower, hupper.trans ?_⟩
  positivity

end Brockian

