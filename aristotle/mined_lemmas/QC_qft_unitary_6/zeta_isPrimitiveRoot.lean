/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma zeta_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := by
  simpa [zeta, mul_assoc, mul_comm, mul_left_comm] using Complex.isPrimitiveRoot_exp n hn

