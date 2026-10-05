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

lemma cfc_posSemidef (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (hA.cfc f).PosSemidef := by
  have hd : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) : Matrix n n 𝕜).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa [Function.comp_def] using (RCLike.ofReal_nonneg (K := 𝕜)).mpr (hf i)
  rw [cfc_eq_conj]
  exact hd.mul_mul_conjTranspose_same _

