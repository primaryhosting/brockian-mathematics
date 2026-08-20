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

lemma stdAddChar_re (m : ZMod n) :
    (stdAddChar m : ℂ).re = Real.cos (2 * Real.pi * m.val / n) := by
  have h : ((m.val : ℤ) : ZMod n) = m := by push_cast [ZMod.natCast_val]; simp
  have h2 : (stdAddChar m : ℂ) = Complex.exp (2 * Real.pi * I * ((m.val : ℤ) : ℂ) / n) := by
    rw [← ZMod.stdAddChar_coe, h]
  have h3 : (2 * (Real.pi : ℂ) * I * ((m.val : ℤ) : ℂ) / n)
      = ((2 * Real.pi * m.val / n : ℝ) : ℂ) * I := by push_cast; ring
  rw [h2, h3, Complex.exp_ofReal_mul_I_re]

end Char

/-! ## The Fourier (discrete) transform and Parseval -/

/-- Reindexing a sum over `ZMod n` by the shift `j ↦ j + 1`. -/
