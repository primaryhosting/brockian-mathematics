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

lemma cycle_energy_lower_bound_real {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℝ)
    (h0 : ∑ j, x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j, (x j) ^ 2 ≤ ∑ j, (x j - x (j + 1)) ^ 2 := by
  have hc0 : ∑ j : ZMod n, ((x j : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, h0]; simp
  have h := cycle_energy_lower_bound hn (fun j => (x j : ℂ)) hc0
  have e1 : ∀ j : ZMod n, ‖((x j : ℂ))‖ ^ 2 = (x j) ^ 2 := by
    intro j; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e2 : ∀ j : ZMod n, ‖((x j : ℂ)) - ((x (j + 1) : ℂ))‖ ^ 2 = (x j - x (j + 1)) ^ 2 := by
    intro j
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [e1, e2] at h
  exact h

/-! ## The quadratic form of the Laplacian -/

