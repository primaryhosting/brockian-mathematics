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

lemma zeta_ne_one {j l : Fin 64} (h : j ≠ l) : zeta ((j : ℕ) - (l : ℕ) : ℂ) ≠ 1 := by
  intro hz
  rw [zeta, Complex.exp_eq_one_iff] at hz
  obtain ⟨n, hn⟩ := hz
  have hd : ((j : ℕ) : ℂ) - (l : ℕ) = (n : ℂ) * 64 := by
    field_simp at hn
    linear_combination hn
  have hd' : ((j : ℕ) : ℤ) - (l : ℕ) = n * 64 := by exact_mod_cast hd
  have hj := j.isLt
  have hl := l.isLt
  have : (j : ℕ) = (l : ℕ) := by omega
  exact h (Fin.ext this)

/-- The 6-qubit quantum Fourier transform matrix is unitary. -/
