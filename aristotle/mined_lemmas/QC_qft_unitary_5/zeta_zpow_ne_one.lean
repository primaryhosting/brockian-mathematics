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

lemma zeta_zpow_ne_one (N : ℕ) (hN : N ≠ 0) {j l : Fin N} (h : j ≠ l) :
    zeta N ^ ((l : ℤ) - (j : ℤ)) ≠ 1 := by
  intro hone
  have hdvd : ((N : ℤ)) ∣ ((l : ℤ) - (j : ℤ)) :=
    ((isPrimitiveRoot_zeta N hN).zpow_eq_one_iff_dvd _).mp hone
  have hjl : (j : ℕ) ≠ (l : ℕ) := fun hh => h (Fin.ext hh)
  have h1 : ((l : ℤ) - (j : ℤ)) ≠ 0 := by
    have : ((j : ℕ) : ℤ) ≠ ((l : ℕ) : ℤ) := by exact_mod_cast hjl
    omega
  have h2 : |(l : ℤ) - (j : ℤ)| < (N : ℤ) := by
    have hj : (j : ℕ) < N := j.isLt
    have hl : (l : ℕ) < N := l.isLt
    have hj' : ((j : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast hj
    have hl' : ((l : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast hl
    have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
    have hl0 : (0 : ℤ) ≤ ((l : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [abs_lt]
    omega
  have := Int.le_of_dvd (abs_pos.mpr h1) ((dvd_abs _ _).mpr hdvd)
  omega

