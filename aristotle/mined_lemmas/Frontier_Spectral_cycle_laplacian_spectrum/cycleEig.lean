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

noncomputable def cycleEig (n : ℕ) : Fin n → ℂ :=
  fun k => ((2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)

/-- The discrete Fourier matrix, whose `k`-th column is the eigenvector
`v k j = exp (2πI k j / n)`. -/
