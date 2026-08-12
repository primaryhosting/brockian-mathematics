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

/-!
# Cosine trace-norm bounds for Hermitian matrices (`CosTraceNorm` family)

For a Hermitian matrix `A` over an `RCLike` field `𝕜` we study the quantity
`cosTrace A = re (trace (cos A))`, where `cos A` is defined by the continuous functional
calculus, and compare it with the trace norm `traceNorm A = re (trace |A|)`
(the sum of the absolute values of the eigenvalues) and with `re (trace (A * A))`
(the squared Frobenius norm).
-/

namespace Brockian

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `cos A`, where `cos A` is defined via the continuous functional calculus. -/
noncomputable def cosTrace (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Matrix.trace (cfc Real.cos A))

/-- The trace norm of a Hermitian matrix: the trace of `|A|`, i.e. the sum of the absolute
values of the eigenvalues of `A`. -/
noncomputable def traceNorm (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Matrix.trace (cfc (fun x : ℝ => |x|) A))

/-- The trace of `f A` (continuous functional calculus) is the sum of `f` over the
eigenvalues. -/
lemma trace_cfc_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (cfc f A) = ((∑ i, f (hA.eigenvalues i) : ℝ) : 𝕜) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  push_cast
  rfl

lemma re_trace_cfc_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (Matrix.trace (cfc f A)) = ∑ i, f (hA.eigenvalues i) := by
  rw [trace_cfc_eq hA f, RCLike.ofReal_re]

lemma cosTrace_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cosTrace A = ∑ i, Real.cos (hA.eigenvalues i) := re_trace_cfc_eq hA _

lemma traceNorm_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := re_trace_cfc_eq hA _

lemma mul_self_eq_cfc_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * A = cfc (fun x : ℝ => x ^ 2) A := by
  have hA' : IsSelfAdjoint A := hA
  rw [cfc_pow (f := fun x : ℝ => x) (ha := hA'), cfc_id' ℝ A hA']
  exact (pow_two A).symm

/-- The squared Frobenius norm of a Hermitian matrix is the sum of the squares of its
eigenvalues. -/
lemma re_trace_sq_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (Matrix.trace (A * A)) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  rw [mul_self_eq_cfc_sq hA, re_trace_cfc_eq hA]

/-- The trace of a Hermitian matrix is the sum of its eigenvalues. -/
lemma re_trace_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (Matrix.trace A) = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues, map_sum]
  simp

/-- Elementary bound: `1 - cos x ≤ x ^ 2 / 2` for all real `x`. -/
lemma one_sub_cos_le_sq_div_two (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h1 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  linarith

/-- Elementary bound: `1 - cos x ≤ |x|` for all real `x`. -/
lemma one_sub_cos_le_abs (x : ℝ) : 1 - Real.cos x ≤ |x| := by
  rcases le_or_gt |x| 2 with h | h
  · have h1 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
    have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [abs_nonneg x]
  · nlinarith [Real.neg_one_le_cos x]

/-- The trace norm of a Hermitian matrix is nonnegative. -/
lemma traceNorm_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) : 0 ≤ traceNorm A := by
  rw [traceNorm_eq hA]
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- `|cosTrace A|` is at most the size of the matrix. -/
lemma abs_cosTrace_le_card {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    |cosTrace A| ≤ (Fintype.card n : ℝ) := by
  rw [cosTrace_eq hA]
  calc |∑ i, Real.cos (hA.eigenvalues i)| ≤ ∑ i, |Real.cos (hA.eigenvalues i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp

/-- The trace of a Hermitian matrix is bounded in absolute value by its trace norm. -/
lemma abs_re_trace_le_traceNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    |RCLike.re (Matrix.trace A)| ≤ traceNorm A := by
  rw [re_trace_eq_sum_eigenvalues hA, traceNorm_eq hA]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The cosine deficiency `n - Tr(cos A)` as a sum over the eigenvalues. -/
lemma card_sub_cosTrace_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (Fintype.card n : ℝ) - cosTrace A = ∑ i, (1 - Real.cos (hA.eigenvalues i)) := by
  rw [cosTrace_eq hA, Finset.sum_sub_distrib]
  simp

/-- **Trace-norm bounds for the cosine of a Hermitian matrix.**
For a Hermitian matrix `A` of size `n`, the deficiency `n - Tr(cos A)` is nonnegative and is
bounded both by the trace norm `Tr|A|` and by half the squared Frobenius norm
`Tr(A²)/2`. -/
theorem CosTraceNorm1597 {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    0 ≤ (Fintype.card n : ℝ) - cosTrace A ∧
      (Fintype.card n : ℝ) - cosTrace A ≤
        min (traceNorm A) (RCLike.re (Matrix.trace (A * A)) / 2) := by
  rw [card_sub_cosTrace_eq hA]
  refine ⟨Finset.sum_nonneg fun i _ => by simpa using Real.cos_le_one (hA.eigenvalues i), ?_⟩
  refine le_min ?_ ?_
  · rw [traceNorm_eq hA]
    exact Finset.sum_le_sum fun i _ => one_sub_cos_le_abs _
  · rw [re_trace_sq_eq hA, Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => one_sub_cos_le_sq_div_two _

/-- Two-sided form: the trace of `cos A` differs from the size of `A` by at most the trace
norm of `A`. -/
theorem CosTraceNorm1597_abs {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    |cosTrace A - (Fintype.card n : ℝ)| ≤ traceNorm A := by
  obtain ⟨h0, h1⟩ := CosTraceNorm1597 hA
  have h2 : (Fintype.card n : ℝ) - cosTrace A ≤ traceNorm A := le_trans h1 (min_le_left _ _)
  rw [abs_le]
  constructor <;> linarith [traceNorm_nonneg hA]

end Brockian

