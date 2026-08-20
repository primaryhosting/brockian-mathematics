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

lemma norm_one_sub_stdAddChar_sq {n : ℕ} [NeZero n] (m : ZMod n) :
    ‖1 - (stdAddChar m : ℂ)‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * m.val / n) := by
  have hz : Complex.normSq (stdAddChar m : ℂ) = 1 := by
    rw [← Complex.sq_norm, norm_stdAddChar]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply] at *
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, ← stdAddChar_re m]
  nlinarith [hz]

/-- The key spectral lower bound in complex form. -/
