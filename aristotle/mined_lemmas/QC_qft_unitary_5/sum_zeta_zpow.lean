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

lemma sum_zeta_zpow (N : ℕ) (hN : N ≠ 0) (j l : Fin N) :
    ∑ k : Fin N, (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ (k : ℕ)
      = if j = l then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (zeta N ^ ((l : ℤ) - (j : ℤ))) ^ k) N]
  by_cases h : j = l
  · subst h
    simp
  · rw [geom_sum_eq (zeta_zpow_ne_one N hN h), zeta_zpow_pow_card N hN j l, if_neg h]
    simp

