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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset SimpleGraph Matrix

/-- The Laplacian of the cycle graph `C n` (`n ≥ 3`) acts on a vector by
`(L v) i = 2 * v i - (v (i-1) + v (i+1))`. -/

lemma cycle_lap_mulVec {n : ℕ} [NeZero n] (hn : 3 ≤ n) (v : Fin n → ℝ) (i : Fin n) :
    ((SimpleGraph.cycleGraph n).lapMatrix ℝ *ᵥ v) i = 2 * v i - (v (i - 1) + v (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset]
  have hne : i - 1 ≠ i + 1 := by
    intro h
    rw [sub_eq_iff_eq_add, add_assoc] at h
    have h0 : (1 + 1 : Fin (m + 3)) = 0 := by
      have : i + (1 + 1) = i + 0 := by rw [← h, add_zero]
      exact add_left_cancel this
    have h2 : ((1 + 1 : Fin (m + 3)) : ℕ) = 2 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt]
    rw [h0] at h2
    simp at h2
  rw [Finset.sum_pair hne]
  norm_num

/-- If `1 ≤ k < n` then `cos (2πk/n) ≤ cos (2π/n)`. -/
