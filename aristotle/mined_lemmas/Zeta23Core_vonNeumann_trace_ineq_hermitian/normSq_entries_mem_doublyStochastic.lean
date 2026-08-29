/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the header above is
-- written as a plain block comment; it is repeated verbatim as a module docstring below.)

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

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `Dₐ W D_b Wᴴ`, for diagonal matrices with real entries `a`, `b`, expands as
`∑ j k, a j * b k * ‖W j k‖ ^ 2`. -/

theorem normSq_entries_mem_doublyStochastic
    (W : Matrix n n 𝕜) (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  have h1 : W * Wᴴ = 1 := by simpa using (Unitary.mem_iff.mp hW).2
  have h2 : Wᴴ * W = 1 := by simpa using (Unitary.mem_iff.mp hW).1
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by dsimp; positivity, fun i => ?_, fun j => ?_⟩
  · have hd : ∑ k, W i k * (Wᴴ) k i = 1 := by
      have := congrFun (congrFun h1 i) i
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have h : ((∑ k, ‖W i k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      rw [RCLike.ofReal_sum, ← hd]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply]
      push_cast
      simpa [RCLike.star_def] using (RCLike.mul_conj (W i k)).symm
    exact_mod_cast h
  · have hd : ∑ k, (Wᴴ) j k * W k j = 1 := by
      have := congrFun (congrFun h2 j) j
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have h : ((∑ k, ‖W k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      rw [RCLike.ofReal_sum, ← hd]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply]
      push_cast
      simpa [RCLike.star_def] using (RCLike.conj_mul (W k j)).symm
    exact_mod_cast h

/-- Averaging a bilinear form against a doubly stochastic matrix cannot beat the value obtained by
pairing the two families in decreasing order.  Here `f` and `g` are antitone families indexed by
`Fin N`, transported to the index type `n` along an equivalence `e`. -/
