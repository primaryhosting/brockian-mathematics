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

lemma sum_normSq_col (W : Matrix n n 𝕜) (h : star W * W = 1) (k : n) :
    ∑ j, ‖W j k‖ ^ 2 = 1 := by
  have hc : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [RCLike.ofReal_sum]
    calc ∑ j, ((‖W j k‖ ^ 2 : ℝ) : 𝕜) = ∑ j, (star W) k j * W j k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.star_apply, RCLike.star_def, RCLike.conj_mul]
          push_cast
          ring
      _ = (star W * W) k k := Matrix.mul_apply.symm
      _ = 1 := by rw [h]; simp
  exact_mod_cast hc

