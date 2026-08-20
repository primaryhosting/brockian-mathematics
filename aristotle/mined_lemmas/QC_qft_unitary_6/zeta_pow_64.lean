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

lemma zeta_pow_64 (d : ℤ) : zeta d ^ 64 = 1 := by
  have : ((64 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * d / 64) = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [zeta, ← Complex.exp_nat_mul, this, Complex.exp_int_mul_two_pi_mul_I]

