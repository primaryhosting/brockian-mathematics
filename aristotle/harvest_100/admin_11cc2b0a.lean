import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- Every diagonal entry of a matrix `U` with `U * Uᴴ = 1` has norm at most `1`:
the `i`-th row of `U` is a unit vector. -/
theorem norm_diag_le_one_of_mul_conjTranspose_eq_one
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U * Uᴴ = 1) (i : n) : ‖U i i‖ ≤ 1 := by
  have h : ∑ j : n, Complex.normSq (U i j) = 1 := by
    have h1 : (U * Uᴴ) i i = 1 := by
      rw [hU]; simp
    rw [Matrix.mul_apply] at h1
    have h2 : ∑ j : n, ((Complex.normSq (U i j) : ℝ) : ℂ) = 1 := by
      rw [← h1]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [Matrix.conjTranspose_apply, Complex.mul_conj]
    exact_mod_cast h2
  have hle : Complex.normSq (U i i) ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun j : n => Complex.normSq (U i j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hsq : ‖U i i‖ ^ 2 ≤ 1 := by
    rwa [Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (U i i)]

/-- **Cosine trace-norm bound.**  If `U` is an `n × n` complex matrix with `U * Uᴴ = 1`
(so its rows are orthonormal) and `θ : n → ℝ` is any family of angles, then the trace of
`U` multiplied by the diagonal matrix of cosines `cos (θ i)` is bounded in norm by
`∑ i, |cos (θ i)|` (in particular by the cardinality of the index type). -/
theorem CosTraceNorm4001 {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (θ : n → ℝ) :
    ‖(U * Matrix.diagonal fun i => (Real.cos (θ i) : ℂ)).trace‖
      ≤ ∑ i : n, |Real.cos (θ i)| := by
  have htr : (U * Matrix.diagonal fun i => (Real.cos (θ i) : ℂ)).trace
      = ∑ i : n, U i i * (Real.cos (θ i) : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  rw [htr]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖U i i‖ ≤ 1 := norm_diag_le_one_of_mul_conjTranspose_eq_one hU i
  nlinarith [abs_nonneg (Real.cos (θ i)), norm_nonneg (U i i)]

/-- The same bound, weakened to the cardinality of the index type. -/
theorem CosTraceNorm4001_card {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (θ : n → ℝ) :
    ‖(U * Matrix.diagonal fun i => (Real.cos (θ i) : ℂ)).trace‖
      ≤ (Fintype.card n : ℝ) := by
  refine le_trans (CosTraceNorm4001 U hU θ) ?_
  have : ∑ _i : n, (1 : ℝ) = (Fintype.card n : ℝ) := by
    simp [Finset.card_univ]
  rw [← this]
  exact Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)

/-- Sanity check: the hypothesis of `CosTraceNorm4001` is satisfiable (the identity matrix). -/
example {n : Type*} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℂ) * (1 : Matrix n n ℂ)ᴴ = 1 := by
  simp

end Brockian

