import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/

theorem dftMatrix_unitary {N : ℕ} (hN : N ≠ 0) :
    dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hc : ((1 / Real.sqrt N : ℝ) : ℂ) * ((1 / Real.sqrt N : ℝ) : ℂ) = 1 / (N : ℂ) := by
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have h1 : (1 / Real.sqrt N : ℝ) * (1 / Real.sqrt N : ℝ) = 1 / (N : ℝ) := by
      rw [div_mul_div_comm, one_mul, hsq]
    rw [← Complex.ofReal_mul, h1]
    push_cast
    ring
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstarc : star ((1 / Real.sqrt N : ℝ) : ℂ) = ((1 / Real.sqrt N : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hterm : ∀ i : Fin N,
      (star (dftMatrix N) j i) * dftMatrix N i k
        = (1 / (N : ℂ)) * omegaRoot N ^ ((((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((i : ℕ) : ℤ)) := by
    intro i
    rw [Matrix.star_apply, dft_entry, dft_entry, star_mul', star_omegaRoot_zpow, hstarc,
      mul_mul_mul_comm, hc, ← zpow_add₀ (omegaRoot_ne_zero N)]
    rw [show -(((i : ℕ) : ℤ) * ((j : ℕ) : ℤ)) + ((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)
        = (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((i : ℕ) : ℤ) by ring]
  simp only [hterm, ← Finset.mul_sum]
  by_cases h : j = k
  · subst h
    simp only [sub_self, zero_mul, zpow_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, if_true]
    field_simp
  · rw [if_neg h]
    have hd : ¬ ((N : ℤ) ∣ (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
      intro hdvd
      have hj : ((j : ℕ) : ℤ) < N := by exact_mod_cast j.isLt
      have hk : ((k : ℕ) : ℤ) < N := by exact_mod_cast k.isLt
      have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
      have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
      have habs : |((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < (N : ℤ) := by
        rw [abs_sub_lt_iff]
        omega
      have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact h (Fin.ext (by omega))
    rw [sum_omega_zpow_eq_zero hN _ hd, mul_zero]

/-- **The n-qubit quantum Fourier transform matrix is unitary.** -/
