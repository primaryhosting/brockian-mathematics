/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QC

/-- The `n`-dimensional quantum Fourier transform matrix:
`(QFT_n)_{j k} = exp(2πi·jk/n) / √n`. -/

lemma conj_mul_entry (n : ℕ) (l j k : ℕ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (l * j) / n)) *
        Complex.exp (2 * Real.pi * Complex.I * (l * k) / n)
      = Complex.exp (2 * Real.pi * Complex.I * (l * ((k : ℤ) - j)) / n) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.ext_iff]
  ring

/-- The QFT matrix satisfies `QFTᴴ * QFT = 1`. -/
