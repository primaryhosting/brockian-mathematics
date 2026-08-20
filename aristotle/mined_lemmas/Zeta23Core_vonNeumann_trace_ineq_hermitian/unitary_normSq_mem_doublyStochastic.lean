import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a unitary matrix `W`, the matrix of squared norms of the entries of `W` is doubly
stochastic: its rows sum to `1` because `W * Wᴴ = 1`, and its columns sum to `1` because
`Wᴴ * W = 1`. -/

lemma unitary_normSq_mem_doublyStochastic {W : Matrix n n 𝕜} (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2) ∈ doublyStochastic ℝ n := by
  have h1 : W * star W = 1 := hW.2
  have h2 : star W * W = 1 := hW.1
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h1 i) i
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def] at h
    have : ((∑ x, ‖W i x‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      simpa [RCLike.mul_conj] using h
    exact_mod_cast this
  · have h := congrFun (congrFun h2 j) j
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def] at h
    have : ((∑ x, ‖W x j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      simpa [RCLike.conj_mul] using h
    exact_mod_cast this

/-- Birkhoff–von Neumann plus rearrangement: if `a` and `b` are antitone and `M` is doubly
stochastic, then `∑ j k, a j * b k * M j k ≤ ∑ i, a i * b i`. -/
