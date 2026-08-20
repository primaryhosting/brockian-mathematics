import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

open Complex Matrix ZMod AddChar Finset

/-- The generating vector of the cycle Laplacian: `2` at `0`, `-1` at `±1`, `0` elsewhere. -/

lemma cycleEigen_eq (k : ZMod n) :
    cycleEigen n k = ((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) := by
  have hk : ((k.val : ℤ) : ZMod n) = k := by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  have h1 : ZMod.stdAddChar k = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / n) := by
    conv_lhs => rw [← hk]
    rw [ZMod.stdAddChar_coe]; push_cast; ring_nf
  have h2 : ZMod.stdAddChar (-k) = Complex.exp (-(2 * Real.pi * I * (k.val : ℂ) / n)) := by
    conv_lhs => rw [← hk, ← Int.cast_neg, ZMod.stdAddChar_coe]
    push_cast; ring_nf
  rw [cycleEigen, h1, h2]
  push_cast
  have h3 := Complex.two_cos ((2 * (Real.pi : ℂ) * (k.val : ℂ) / n))
  rw [neg_mul] at h3
  rw [show (2 * (Real.pi : ℂ) * I * (k.val : ℂ) / n)
      = ((2 * (Real.pi : ℂ) * (k.val : ℂ) / n) * I) by ring]
  linear_combination h3

/-- The cycle Laplacian is conjugate, via the Fourier matrix, to the diagonal matrix of
eigenvalues. -/
