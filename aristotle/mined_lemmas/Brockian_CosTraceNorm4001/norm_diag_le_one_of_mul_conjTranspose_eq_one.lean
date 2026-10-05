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
