/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as a plain block comment; its text is verbatim.)

import Mathlib

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

open Finset Complex ZMod Matrix

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian matrix of the cycle graph `C n`, with vertex set `ZMod n`:
`2` on the diagonal, `-1` between neighbours `i` and `i ± 1`, `0` elsewhere. -/

lemma cos_le_cos_two_pi_div_aux (n v : ℕ) (h1 : 1 ≤ v) (h2 : 2 * v ≤ n) (hn : 3 ≤ n) :
    Real.cos (2 * Real.pi * v / n) ≤ Real.cos (2 * Real.pi / n) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast h1
  have hv2 : 2 * (v:ℝ) ≤ n := by exact_mod_cast h2
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hn0]
    nlinarith [Real.pi_pos]
  · rw [div_le_div_iff_of_pos_right hn0]
    nlinarith [Real.pi_pos]

/-- For `1 ≤ v ≤ n - 1` the cosine `cos (2π v / n)` is at most `cos (2π / n)`. -/
