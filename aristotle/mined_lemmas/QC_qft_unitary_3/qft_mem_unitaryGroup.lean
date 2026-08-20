/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- The (normalized) discrete Fourier transform matrix of size `N` built from a
complex number `z`: its `(j, k)` entry is `z ^ (j * k) / √N`. -/

theorem qft_mem_unitaryGroup (n : ℕ) :
    qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  exact dftMatrix_mem_unitaryGroup (2 ^ n) _
    (Complex.isPrimitiveRoot_exp (2 ^ n) (by positivity))

/-- **The 3-qubit QFT matrix is unitary.** -/
