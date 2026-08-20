/-
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
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

open Complex Finset Matrix

/-! ## Definitions -/

/-- The `n`-th root of unity `exp (2πI/n)`. -/

theorem zetaN_pow_add_inv {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zetaN n ^ k + (zetaN n ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz : zetaN n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [zetaN, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hz' : (zetaN n ^ k)⁻¹ = Complex.exp (-((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [hz, ← Complex.exp_neg]
    congr 1
    ring
  rw [hz', hz, ← Complex.two_cos]
  push_cast
  ring

/-! ## Invertibility of the DFT matrix -/

