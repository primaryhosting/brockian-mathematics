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

noncomputable def dftMatrix (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => z ^ (j.val * k.val) / Real.sqrt N

/-- The quantum Fourier transform matrix on `n` qubits, i.e. the `2 ^ n`-dimensional
DFT matrix with `z = exp (2 π i / 2 ^ n)`:
`(QFT_n)_{j,k} = exp (2 π i j k / 2 ^ n) / √(2 ^ n)`. -/
