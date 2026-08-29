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
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic definitions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr (Mᴴ M)`. -/

lemma hFun_posSemidef {g : ℝ → ℝ} (hg : ∀ i, 0 ≤ g (hA.eigenvalues i)) :
    (hFun hA g).PosSemidef := by
  have hd : (diagonal (fun i => (RCLike.ofReal (g (hA.eigenvalues i)) : 𝕜))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    have : (0:ℝ) ≤ g (hA.eigenvalues i) := hg i
    simpa using RCLike.ofReal_nonneg (K := 𝕜) |>.mpr this
  have := hd.mul_mul_conjTranspose_same (B := (hA.eigenvectorUnitary : Matrix n n 𝕜))
  simpa [hFun, Matrix.star_eq_conjTranspose] using this

/-! ## Generalities on the Frobenius norm and traces -/

omit [DecidableEq n] in
