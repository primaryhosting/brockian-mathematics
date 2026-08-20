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

lemma sum_eq_zero_of_eigen {μ : ℝ} (hμ : μ ≠ 0) {x : Fin (m + 3) → ℝ}
    (hx : (SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x = μ • x) :
    ∑ i : Fin (m + 3), x i = 0 := by
  have hsum : ∑ i : Fin (m + 3), ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i
      = μ * ∑ i : Fin (m + 3), x i := by
    rw [hx]
    simp [Finset.mul_sum]
  rw [show (∑ i : Fin (m + 3), ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i)
      = ∑ i : Fin (m + 3), (2 * x i - x (i - 1) - x (i + 1)) from
    Finset.sum_congr rfl fun i _ => lap_mulVec m x i] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, shift_sum m x,
    shift_sum' m x] at hsum
  have hz : μ * ∑ i : Fin (m + 3), x i = 0 := by linarith
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hμ
  · exact h

end CycleAux

open CycleAux in
/-- **Fiedler value of the cycle graph.**  For `n ≥ 3` the algebraic connectivity of the cycle
`C n` equals `2 - 2 cos (2π/n)`: it is the least Rayleigh quotient of the Laplacian over nonzero
vectors orthogonal to the all-ones vector, and equivalently the least nonzero eigenvalue of the
Laplacian. -/
