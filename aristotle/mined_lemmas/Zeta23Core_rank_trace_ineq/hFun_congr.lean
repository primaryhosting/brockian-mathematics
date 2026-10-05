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

lemma hFun_congr {g h : ℝ → ℝ} (hgh : ∀ i, g (hA.eigenvalues i) = h (hA.eigenvalues i)) :
    hFun hA g = hFun hA h := by
  have h' : (fun i => (RCLike.ofReal (g (hA.eigenvalues i)) : 𝕜))
      = fun i => (RCLike.ofReal (h (hA.eigenvalues i)) : 𝕜) := funext fun i => by rw [hgh i]
  simp only [hFun, h']

