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

lemma stdAddChar_re (k : ZMod N) :
    (ZMod.stdAddChar k).re = Real.cos (2 * Real.pi * k.val / N) := by
  have hk : k = ((k.val : ℤ) : ZMod N) := by push_cast [ZMod.natCast_val]; simp
  have h1 : ZMod.stdAddChar k
      = Complex.exp (((2 * Real.pi * k.val / N : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hk]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [h1, Complex.exp_ofReal_mul_I_re]

/-- For `z` of modulus one, `‖1 - z‖ ^ 2 = 2 - 2 * z.re`. -/
