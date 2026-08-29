/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)` used in the QFT. -/

lemma qftOmega_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (qftOmega n) n :=
  Complex.isPrimitiveRoot_exp n hn

