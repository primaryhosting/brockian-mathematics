/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/

lemma qftOmega_pow : qftOmega ^ (128 : ℕ) = 1 := qftOmega_prim.pow_eq_one

