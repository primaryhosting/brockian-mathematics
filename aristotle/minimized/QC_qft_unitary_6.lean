import Mathlib

/-!
# Unitarity of the 6-qubit Quantum Fourier Transform

The quantum Fourier transform on `n = 6` qubits acts on the `2^6 = 64` dimensional
state space.  Its matrix has entries

`F j k = (1 / √64) * exp (2πi * j * k / 64) = (1/8) * exp (2πi * j * k / 64)`.

We prove that this matrix is unitary, i.e. it belongs to `Matrix.unitaryGroup (Fin 64) ℂ`.
-/

namespace QC

open Complex Finset

/-- The `6`-qubit quantum Fourier transform matrix, acting on the `2 ^ 6 = 64`
dimensional space of computational basis states.  The normalisation factor is
`1 / √64 = 1 / 8`. -/

noncomputable def qft6 : Matrix (Fin 64) (Fin 64) ℂ := fun j k =>
  (1 / 8 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / 64)

/-- Complex conjugation of a `64`-th root of unity of the shape used in `qft6`. -/
