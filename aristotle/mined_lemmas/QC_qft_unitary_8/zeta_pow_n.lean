/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma zeta_pow_n (n : ℕ) (hn : n ≠ 0) : zeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

