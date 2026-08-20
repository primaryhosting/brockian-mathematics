import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `16`-th root of unity `e^{2πi/16}` used by the 4-qubit QFT
(`N = 2^4 = 16`). -/

lemma ratio_eq_one_iff (k l : Fin 16) :
    omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹ = 1 ↔ k = l := by
  have hne : omega16 ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  constructor
  · intro h
    have : omega16 ^ (k : ℕ) = omega16 ^ (l : ℕ) := by
      field_simp at h
      exact h
    exact Fin.ext (isPrimitiveRoot_omega16.pow_inj k.isLt l.isLt this)
  · rintro rfl
    field_simp

/-- The key orthogonality relation: the geometric sum of the ratio over all
`16` indices is `16` when `k = l` and `0` otherwise. -/
