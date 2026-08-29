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

theorem cycle_fiedler_value_rayleigh (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    IsLeast {r : ℝ | ∃ v : ZMod n → ℝ, v ≠ 0 ∧ (∑ i : ZMod n, v i = 0) ∧
        r = (∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i) / ∑ i : ZMod n, (v i) ^ 2}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  constructor
  · refine ⟨fiedlerVector n, fiedlerVector_ne_zero, sum_fiedlerVector hn, ?_⟩
    have hpos : 0 < ∑ i : ZMod n, (fiedlerVector n i) ^ 2 := sum_sq_pos fiedlerVector_ne_zero
    have hq : ∑ i : ZMod n, fiedlerVector n i * (cycleLaplacian n).mulVec (fiedlerVector n) i
        = (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ i : ZMod n, (fiedlerVector n i) ^ 2 := by
      rw [cycleLaplacian_mulVec_fiedlerVector hn, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring
    rw [hq]
    field_simp
  · rintro r ⟨v, hv0, hvsum, rfl⟩
    have hpos : 0 < ∑ i : ZMod n, (v i) ^ 2 := sum_sq_pos hv0
    rw [le_div_iff₀ hpos, cycleLaplacian_quadratic_form hn]
    exact energy_lower_bound_real hn v hvsum

end Frontier.Spectral

