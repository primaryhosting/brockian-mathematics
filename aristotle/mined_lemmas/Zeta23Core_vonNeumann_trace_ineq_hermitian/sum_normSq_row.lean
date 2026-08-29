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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

section Rearrangement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Value of the bilinear form `M ↦ ∑ j, ∑ k, M j k * (a j * b k)` at a permutation matrix. -/

lemma sum_normSq_row (W : Matrix n n 𝕜) (h : W * star W = 1) (j : n) :
    ∑ k, ‖W j k‖ ^ 2 = 1 := by
  have hc : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [RCLike.ofReal_sum]
    calc ∑ k, ((‖W j k‖ ^ 2 : ℝ) : 𝕜) = ∑ k, W j k * (star W) k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj]
          push_cast
          ring
      _ = (W * star W) j j := Matrix.mul_apply.symm
      _ = 1 := by rw [h]; simp
  exact_mod_cast hc

/-- Column sums of `|W_{jk}|²` for a matrix `W` with `W⋆ * W = 1`. -/
