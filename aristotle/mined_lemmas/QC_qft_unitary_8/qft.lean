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

/-- The `N × N` Quantum Fourier Transform matrix:
`(QFT N) j k = exp (2 π i j k / N) / √N`. -/

noncomputable def qft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => Complex.exp (2 * Real.pi * Complex.I * (j * k) / N) / Real.sqrt N

section
variable {N : ℕ}

/-- The `(a, b)` "phase" of the QFT: `exp (2 π i (b - a) / N)`. -/
private noncomputable def phase (N : ℕ) (a b : Fin N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((b : ℕ) - (a : ℕ)) / N)

