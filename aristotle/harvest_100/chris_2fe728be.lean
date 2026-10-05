/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The trace norm (Schatten `1`-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/
noncomputable def traceNorm (hA : A.IsHermitian) : ℝ := ∑ i, |hA.eigenvalues i|

/-- The Hilbert–Schmidt (Frobenius) norm squared of a Hermitian matrix, expressed
spectrally as the sum of the squares of its eigenvalues. -/
noncomputable def hsNormSq (hA : A.IsHermitian) : ℝ := ∑ i, (hA.eigenvalues i) ^ 2

/-- The trace of `f(A)` (continuous functional calculus of a Hermitian matrix `A`) is the
sum of `f` over the eigenvalues of `A`. -/
lemma trace_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self]
  rw [one_mul, Matrix.trace_diagonal]
  push_cast
  simp [Function.comp_def]

/-- The trace of `cos (t • A)` for a Hermitian matrix `A` is real, equal to the sum of
`cos (t * λ)` over the eigenvalues `λ` of `A`. -/
lemma trace_cos_smul (hA : A.IsHermitian) (t : ℝ) :
    (cfc (fun x : ℝ => Real.cos (t * x)) A).trace
      = ((∑ i, Real.cos (t * hA.eigenvalues i) : ℝ) : ℂ) :=
  trace_cfc hA _

/-- Pointwise bound: `|cos y - 1| ≤ |y|`. -/
lemma abs_cos_sub_one_le (y : ℝ) : |Real.cos y - 1| ≤ |y| := by
  simpa using Real.abs_cos_sub_cos_le y 0

/-- Pointwise bound: `|cos y - 1| ≤ y ^ 2 / 2`. -/
lemma abs_cos_sub_one_le_sq (y : ℝ) : |Real.cos y - 1| ≤ y ^ 2 / 2 := by
  have h1 : Real.cos y ≤ 1 := Real.cos_le_one y
  have h2 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  rw [abs_le]
  constructor <;> linarith

/-- **Cos Trace Norm 1597.**

For a Hermitian matrix `A` and a real parameter `t`, the trace of `cos (t A)` (defined by
the continuous functional calculus) deviates from the trace of the identity by at most
`|t|` times the trace norm of `A`:
`‖Tr cos (t A) - n‖ ≤ |t| · ‖A‖₁`. -/
theorem CosTraceNorm1597 (hA : A.IsHermitian) (t : ℝ) :
    ‖(cfc (fun x : ℝ => Real.cos (t * x)) A).trace - (Fintype.card n : ℂ)‖
      ≤ |t| * traceNorm hA := by
  have hcard : ((Fintype.card n : ℂ)) = ((∑ _i : n, (1 : ℝ) : ℝ) : ℂ) := by
    simp [Finset.card_univ]
  rw [trace_cos_smul hA, hcard, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  calc |∑ i, (Real.cos (t * hA.eigenvalues i) - 1)|
      ≤ ∑ i, |Real.cos (t * hA.eigenvalues i) - 1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |t| * |hA.eigenvalues i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [abs_mul] using abs_cos_sub_one_le (t * hA.eigenvalues i)
    _ = |t| * traceNorm hA := by rw [traceNorm, Finset.mul_sum]

/-- A companion quadratic bound: `‖Tr cos (t A) - n‖ ≤ (t ^ 2 / 2) · ‖A‖₂²`, where `‖A‖₂²`
is the sum of the squares of the eigenvalues of `A`. -/
theorem CosTraceNorm1597_quadratic (hA : A.IsHermitian) (t : ℝ) :
    ‖(cfc (fun x : ℝ => Real.cos (t * x)) A).trace - (Fintype.card n : ℂ)‖
      ≤ t ^ 2 / 2 * hsNormSq hA := by
  have hcard : ((Fintype.card n : ℂ)) = ((∑ _i : n, (1 : ℝ) : ℝ) : ℂ) := by
    simp [Finset.card_univ]
  rw [trace_cos_smul hA, hcard, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  calc |∑ i, (Real.cos (t * hA.eigenvalues i) - 1)|
      ≤ ∑ i, |Real.cos (t * hA.eigenvalues i) - 1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, t ^ 2 / 2 * (hA.eigenvalues i) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := abs_cos_sub_one_le_sq (t * hA.eigenvalues i)
        calc |Real.cos (t * hA.eigenvalues i) - 1| ≤ (t * hA.eigenvalues i) ^ 2 / 2 := this
          _ = t ^ 2 / 2 * (hA.eigenvalues i) ^ 2 := by ring
    _ = t ^ 2 / 2 * hsNormSq hA := by rw [hsNormSq, Finset.mul_sum]

end Brockian

