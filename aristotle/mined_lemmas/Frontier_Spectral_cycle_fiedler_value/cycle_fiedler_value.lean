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

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

theorem cycle_fiedler_value (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    IsLeast {μ : ℝ | ∃ v : ZMod n → ℝ, v ≠ 0 ∧ (∑ i : ZMod n, v i = 0) ∧
        (cycleLaplacian n).mulVec v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  constructor
  · exact ⟨fiedlerVector n, fiedlerVector_ne_zero, sum_fiedlerVector hn,
      cycleLaplacian_mulVec_fiedlerVector hn⟩
  · rintro μ ⟨v, hv0, hvsum, hvL⟩
    have hpos : 0 < ∑ i : ZMod n, (v i) ^ 2 := sum_sq_pos hv0
    have hquad : ∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i = μ * ∑ i : ZMod n, (v i) ^ 2 := by
      rw [hvL]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring
    rw [cycleLaplacian_quadratic_form hn] at hquad
    have hlb := energy_lower_bound_real hn v hvsum
    rw [hquad] at hlb
    exact le_of_mul_le_mul_right (by linarith) hpos

/-- **Variational form of the Fiedler value of the cycle graph.**
For `n ≥ 3`, the minimum of the Rayleigh quotient of the cycle Laplacian over all nonzero
vectors orthogonal to the all-ones vector equals `2 - 2 * cos (2π/n)`. -/
