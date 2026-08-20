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

noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  dftMatrix (2 ^ n) (Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ)))

/-- If `z` is a primitive `N`-th root of unity, the normalized DFT matrix of size `N`
is unitary. -/
