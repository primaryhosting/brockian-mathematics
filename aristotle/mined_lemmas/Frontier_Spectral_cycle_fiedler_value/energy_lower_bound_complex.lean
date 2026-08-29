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

lemma energy_lower_bound_complex (h3 : 3 ≤ n) (u : ZMod n → ℂ) (hu : ∑ j : ZMod n, u j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j : ZMod n, ‖u j‖ ^ 2
      ≤ ∑ j : ZMod n, ‖u j - u (j + 1)‖ ^ 2 := by
  set c : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n) with hc
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hU0 : 𝓕 u 0 = 0 := by rw [ZMod.dft_apply_zero]; exact hu
  have hkey : ∀ k : ZMod n, c * ‖𝓕 u k‖ ^ 2 ≤ ‖𝓕 (fun j => u j - u (j + 1)) k‖ ^ 2 := by
    intro k
    rw [dft_diff, norm_mul, mul_pow]
    by_cases hk : k = 0
    · subst hk; simp [hU0]
    · exact mul_le_mul_of_nonneg_right (fiedler_le_norm_one_sub_char hk) (by positivity)
  have hsum : c * ∑ k : ZMod n, ‖𝓕 u k‖ ^ 2
      ≤ ∑ k : ZMod n, ‖𝓕 (fun j => u j - u (j + 1)) k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hkey k
  rw [dft_parseval, dft_parseval] at hsum
  have := (mul_le_mul_iff_of_pos_left hn0).mp (by linarith : (n : ℝ) * (c * ∑ j : ZMod n, ‖u j‖ ^ 2)
    ≤ (n : ℝ) * ∑ j : ZMod n, ‖u j - u (j + 1)‖ ^ 2)
  exact this

/-- Spectral gap inequality (real form). -/
