/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi / N)` used in the QFT. -/

lemma qftRoot_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (qftRoot N) N :=
  Complex.isPrimitiveRoot_exp N hN

