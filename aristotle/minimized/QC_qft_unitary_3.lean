/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

open Complex

/-- The primitive 8-th root of unity `exp(2πi/8)`. -/

noncomputable def omega8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix, of size `8 × 8`, with entries
`ω^(j*k) / √8` where `ω = exp(2πi/8)`. -/

noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => omega8 ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt 8 : ℝ)
