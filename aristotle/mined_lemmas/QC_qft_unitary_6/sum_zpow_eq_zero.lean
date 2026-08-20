import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp(2πi/n)` used in the quantum Fourier transform. -/

private lemma sum_zpow_eq_zero (d : ℤ) (h : ¬ ((64 : ℤ) ∣ d)) :
    ∑ k : Fin 64, (qftOmega 64 ^ d) ^ (k : ℕ) = 0 := by
  set η : ℂ := qftOmega 64 ^ d with hη
  have hne : η ≠ 1 := by
    rw [hη]
    intro hc
    exact h ((zeta_prim.zpow_eq_one_iff_dvd d).mp hc)
  have hpow : η ^ 64 = 1 := by
    rw [hη, ← zpow_natCast (qftOmega 64 ^ d) 64, ← _root_.zpow_mul]
    rw [zeta_prim.zpow_eq_one_iff_dvd]
    exact ⟨d, by ring⟩
  have : ∑ k ∈ Finset.range 64, η ^ k = (η ^ 64 - 1) / (η - 1) := geom_sum_eq hne 64
  rw [Fin.sum_univ_eq_sum_range (fun k => η ^ k) 64, this, hpow]
  simp

/-- The 6-qubit (64-dimensional) quantum Fourier transform matrix is unitary. -/
