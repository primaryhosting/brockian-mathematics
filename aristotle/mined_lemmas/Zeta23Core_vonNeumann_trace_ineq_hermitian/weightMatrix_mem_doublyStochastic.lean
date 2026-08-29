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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of `W`. If `W` is unitary this is a doubly
stochastic matrix. -/

lemma weightMatrix_mem_doublyStochastic {W : Matrix n n 𝕜}
    (h₁ : W * star W = 1) (h₂ : star W * W = 1) :
    weightMatrix W ∈ doublyStochastic ℝ n := by
  have hz : ∀ z : 𝕜, z * star z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    intro z; rw [RCLike.star_def, RCLike.mul_conj]; push_cast; ring
  have hz' : ∀ z : 𝕜, star z * z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    intro z; rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring
  refine mem_doublyStochastic_iff_sum.2 ⟨fun j k => by rw [weightMatrix_apply]; positivity, fun j => ?_, fun k => ?_⟩
  · have h := congrFun (congrFun h₁ j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, hz, Matrix.one_apply_eq, ← RCLike.ofReal_sum] at h
    simpa using (by exact_mod_cast h : ∑ k, ‖W j k‖ ^ 2 = (1 : ℝ))
  · have h := congrFun (congrFun h₂ k) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, hz', Matrix.one_apply_eq, ← RCLike.ofReal_sum] at h
    simpa using (by exact_mod_cast h : ∑ j, ‖W j k‖ ^ 2 = (1 : ℝ))

/-- Maximizing the bilinear form `S ↦ ∑ⱼₖ aⱼ b_k Sⱼₖ` over doubly stochastic matrices:
by Birkhoff's theorem `S` is a convex combination of permutation matrices, and for each
permutation the rearrangement inequality applies. -/
