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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/

lemma zeta_pow_card (k : ℕ) : (zeta n k) ^ n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [zeta, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * k / n) = (k : ℤ) * (2 * Real.pi * Complex.I) := by
    field_simp
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

