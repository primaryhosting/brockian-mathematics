import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

/-- The real part of the trace of a matrix. -/

lemma cfc_isHermitian (hA : A.IsHermitian) (f : ℝ → ℝ) : (hA.cfc f).IsHermitian := by
  have hD : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) : Matrix n n 𝕜)ᴴ
      = diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) := by
    simp [Matrix.diagonal_conjTranspose, Function.comp_def, Pi.star_def]
  unfold Matrix.IsHermitian
  rw [cfc_eq_conj]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]

