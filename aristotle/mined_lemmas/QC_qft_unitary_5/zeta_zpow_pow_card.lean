/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma zeta_zpow_pow_card (N : ℕ) (hN : N ≠ 0) (j l : Fin N) :
    (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ N = 1 := by
  rw [← zpow_natCast (zeta N ^ ((l : ℤ) - (j : ℤ))) N, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, zpow_natCast, (isPrimitiveRoot_zeta N hN).pow_eq_one, _root_.one_zpow]

/-- Orthogonality of the columns of the DFT matrix: the geometric sum of the powers of
`ζ^(l-j)` is `N` when `j = l` and `0` otherwise. -/
