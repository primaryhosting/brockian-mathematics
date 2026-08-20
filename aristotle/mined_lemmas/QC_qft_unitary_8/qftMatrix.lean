/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex Real ZMod AddChar

namespace QC

/-- The `N × N` quantum Fourier transform matrix, indexed by `ZMod N`:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/

noncomputable def qftMatrix (N : ℕ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun j k => Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N) / Real.sqrt N

/-- The entries of the QFT matrix in terms of the standard additive character of `ZMod N`. -/
