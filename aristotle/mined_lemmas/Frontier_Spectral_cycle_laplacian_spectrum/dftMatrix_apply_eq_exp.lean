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

theorem dftMatrix_apply_eq_exp {n : ℕ} (hn : n ≠ 0) (j k : Fin n) :
    dftMatrix n j k
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℕ) * (j : ℕ) / (n : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [dftMatrix, zetaN, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The discrete Fourier vectors `v k j = exp (2πI k j / n)` are eigenvectors of the cycle
Laplacian, with eigenvalue `2 - 2 cos (2πk/n)`. -/
