/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma stdAddChar_add_neg (k : ZMod n) :
    ZMod.stdAddChar k + ZMod.stdAddChar (-k) = 2 * Real.cos (2 * Real.pi * k.val / n) := by
  have hk : (ZMod.stdAddChar k : ℂ) = Complex.exp (2 * Real.pi * Complex.I * k.val / n) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hneg : (ZMod.stdAddChar (-k) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * ((-(k.val : ℤ) : ℤ) : ℂ) / n) := by
    rw [← ZMod.stdAddChar_coe]
    congr 1
    push_cast
    simp [ZMod.natCast_val]
  rw [hk, hneg]
  set t : ℝ := 2 * Real.pi * k.val / n with ht
  have e1 : (2 : ℂ) * Real.pi * Complex.I * k.val / n = (t : ℂ) * Complex.I := by
    rw [ht]; push_cast; ring
  have e2 : (2 : ℂ) * Real.pi * Complex.I * ((-(k.val : ℤ) : ℤ) : ℂ) / n
      = -((t : ℂ) * Complex.I) := by
    rw [ht]; push_cast; ring
  rw [e1, e2, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos]
  ring

