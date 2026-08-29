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

lemma cfc_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f * hA.cfc g = hA.cfc (fun x => f x * g x) := by
  have hd : (fun i => (RCLike.ofReal ∘ f ∘ hA.eigenvalues) i *
        (RCLike.ofReal ∘ g ∘ hA.eigenvalues) i)
      = (RCLike.ofReal ∘ (fun x => f x * g x) ∘ hA.eigenvalues : n → 𝕜) := by
    funext i; simp [Function.comp_def]
  rw [cfc_eq_conj, cfc_eq_conj, cfc_eq_conj, conj_mul_conj, Matrix.diagonal_mul_diagonal, hd]

