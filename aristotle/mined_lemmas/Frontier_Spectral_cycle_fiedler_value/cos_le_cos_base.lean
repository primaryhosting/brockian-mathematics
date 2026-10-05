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

lemma cos_le_cos_base {n m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    Real.cos (2 * Real.pi * m / n) ≤ Real.cos (2 * Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  set θ : ℝ := 2 * Real.pi * m / n with hθ
  have hbase : 0 ≤ 2 * Real.pi / n := by positivity
  rcases le_total θ Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hbase h (by
      rw [hθ, div_le_div_iff_of_pos_right hn0]; nlinarith)
  · rw [show Real.cos θ = Real.cos (2 * Real.pi - θ) from (Real.cos_two_pi_sub θ).symm]
    refine Real.cos_le_cos_of_nonneg_of_le_pi hbase (by linarith) ?_
    have heq : 2 * Real.pi - θ = 2 * Real.pi * ((n : ℝ) - m) / n := by rw [hθ]; field_simp
    rw [heq, div_le_div_iff_of_pos_right hn0]
    nlinarith

variable {n : ℕ} [NeZero n]

/-- The nonzero Fourier modes all have `‖1 - χ(k)‖ ^ 2` at least the Fiedler value. -/
