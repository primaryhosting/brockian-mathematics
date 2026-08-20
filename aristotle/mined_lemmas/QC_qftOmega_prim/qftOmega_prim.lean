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

lemma qftOmega_prim : IsPrimitiveRoot qftOmega 128 :=
  Complex.isPrimitiveRoot_exp 128 (by norm_num)

