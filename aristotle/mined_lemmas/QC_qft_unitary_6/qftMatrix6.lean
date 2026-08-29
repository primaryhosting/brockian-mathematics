/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `64`-th root of unity `exp (2πi/64)` used by the 6-qubit QFT. -/

noncomputable def qftMatrix6 : Matrix (Fin 64) (Fin 64) ℂ :=
  fun j k => qftOmega ^ (j.val * k.val) / 8

