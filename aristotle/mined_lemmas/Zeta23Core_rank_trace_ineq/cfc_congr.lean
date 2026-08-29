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

lemma cfc_congr (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) : hA.cfc f = hA.cfc g := by
  have hd : (RCLike.ofReal ∘ f ∘ hA.eigenvalues : n → 𝕜)
      = (RCLike.ofReal ∘ g ∘ hA.eigenvalues : n → 𝕜) := by
    funext i; simp [Function.comp_def, h i]
  rw [cfc_eq_conj, cfc_eq_conj, hd]

