/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

lemma sqAbs_mem_doublyStochastic {W : Matrix n n 𝕜} (h1 : W * star W = 1)
    (h2 : star W * W = 1) :
    (Matrix.of fun p q => ‖W p q‖ ^ 2) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj, Matrix.one_apply_eq] at h
    have hc : ((∑ q, ‖W i q‖ ^ 2 : ℝ) : 𝕜) = (1 : 𝕜) := by push_cast; simpa using h
    simpa using (by exact_mod_cast hc : (∑ q, ‖W i q‖ ^ 2 : ℝ) = 1)
  · have h := congrFun (congrFun h2 j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, RCLike.conj_mul, Matrix.one_apply_eq] at h
    have hc : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : 𝕜) = (1 : 𝕜) := by push_cast; simpa using h
    simpa using (by exact_mod_cast hc : (∑ i, ‖W i j‖ ^ 2 : ℝ) = 1)

/-- Expansion of the trace of `diagonal da * W * diagonal db * Wᴴ`. -/
