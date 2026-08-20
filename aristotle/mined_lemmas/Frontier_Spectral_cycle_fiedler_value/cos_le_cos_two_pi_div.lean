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

lemma cos_le_cos_two_pi_div (n v : ℕ) (h1 : 1 ≤ v) (h2 : v ≤ n - 1) (hn : 3 ≤ n) :
    Real.cos (2 * Real.pi * v / n) ≤ Real.cos (2 * Real.pi / n) := by
  by_cases h : 2 * v ≤ n
  · exact cos_le_cos_two_pi_div_aux n v h1 h hn
  · have hvn : v ≤ n := by omega
    have hw : Real.cos (2 * Real.pi * v / n) = Real.cos (2 * Real.pi * (n - v : ℕ) / n) := by
      have hrw : (2 * Real.pi * ((n - v : ℕ) : ℝ) / n) = 2 * Real.pi - 2 * Real.pi * v / n := by
        have hcast : ((n - v : ℕ) : ℝ) = (n : ℝ) - v := by
          have := Nat.cast_sub hvn (R := ℝ); simpa using this
        rw [hcast]
        field_simp
      rw [hrw, Real.cos_two_pi_sub]
    rw [hw]
    exact cos_le_cos_two_pi_div_aux n (n - v) (by omega) (by omega) hn

