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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix Finset

/-! ### A rearrangement bound for doubly stochastic matrices -/

/-- If `a` and `b` monovary, then the bilinear form `∑ j k, D j k * (a j * b k)` attached to a
doubly stochastic matrix `D` is at most `∑ i, a i * b i`.  This is the combinatorial heart of the
von Neumann trace inequality: it follows from Birkhoff's theorem together with the rearrangement
inequality. -/

lemma normSq_mem_doublyStochastic {M : Matrix n n 𝕜} (h1 : M * Mᴴ = 1) (h2 : Mᴴ * M = 1) :
    (Matrix.of fun j k => ‖M j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp only [Matrix.of_apply]; positivity, fun j => ?_, fun k => ?_⟩
  · have h := congrFun (congrFun h1 j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ k, ‖M j k‖ ^ 2 : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜) := by
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
    simpa using RCLike.ofReal_injective hc
  · have h := congrFun (congrFun h2 k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ j, ‖M j k‖ ^ 2 : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜) := by
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def, mul_comm, RCLike.mul_conj]
    simpa using RCLike.ofReal_injective hc

/-- Expansion of `tr (Dₐ M D_b Mᴴ)` for real diagonal matrices `Dₐ`, `D_b`. -/
