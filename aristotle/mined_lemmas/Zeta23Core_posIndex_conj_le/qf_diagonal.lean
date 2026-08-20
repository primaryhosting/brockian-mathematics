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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Matrix

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form attached to a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

theorem qf_diagonal {m : Type*} [Fintype m] [DecidableEq m] (l : m → ℝ) (y : m → 𝕜) :
    qf (Matrix.diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ l)) y = ∑ i, l i * ‖y i‖ ^ 2 := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def,
    Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (starRingEnd 𝕜) (y i) * ((l i : 𝕜) * y i)
      = (l i : 𝕜) * ((starRingEnd 𝕜) (y i) * y i) by ring, RCLike.conj_mul]
  simp

/-- Diagonalization of the quadratic form of a Hermitian matrix: in the coordinates given by
the eigenvector unitary, the form is the weighted sum of squares with the eigenvalues as weights. -/
