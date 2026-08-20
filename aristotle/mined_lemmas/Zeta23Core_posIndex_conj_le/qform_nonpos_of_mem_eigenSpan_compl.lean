import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- Unfolding lemma for `Matrix.toEuclideanLin`. -/

lemma qform_nonpos_of_mem_eigenSpan_compl {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    {x : EuclideanSpace 𝕜 m} (hx : x ∈ eigenSpan hQ (posSet hQ)ᶜ) : qform Q x ≤ 0 := by
  rw [qform_eq_sum hQ]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ (posSet hQ)ᶜ
  · have hle : hQ.eigenvalues i ≤ 0 := by
      simp only [Finset.mem_compl, posSet, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hi
      exact hi
    have h2 : (0:ℝ) ≤ ‖inner 𝕜 (hQ.eigenvectorBasis i) x‖ ^ 2 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg hle h2
  · rw [inner_eq_zero_of_mem_eigenSpan hQ _ hx hi]
    simp

/-- Hard direction of Sylvester's law of inertia: any subspace on which `Q` is positive definite
has dimension at most `n₊(Q)`. -/
