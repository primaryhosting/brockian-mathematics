import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma dotProduct_pos {x : Fin (m + 3) → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hx

/-- Any eigenvector for a nonzero eigenvalue of the cycle Laplacian sums to zero. -/
