import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `2^n`-th root of unity used by the quantum Fourier transform. -/

lemma qftRoot_pow_card (n : ℕ) : (qftRoot n) ^ (2 ^ n) = 1 :=
  (qftRoot_isPrimitiveRoot n).pow_eq_one

