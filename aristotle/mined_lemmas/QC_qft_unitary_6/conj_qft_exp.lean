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

lemma conj_qft_exp (a b : ℕ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (a * b) / 64))
      = Complex.exp (-(2 * Real.pi * Complex.I * (a * b) / 64)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal,
    Complex.conj_natCast]
  ring

/-- The `64`-th root of unity attached to a difference of indices. -/
