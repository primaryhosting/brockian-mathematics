import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace QC

/-- The `N × N` quantum Fourier transform matrix:
`(QFT_N) j k = N^(-1/2) * exp (2πi jk / N)`. -/

theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = ((N : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, Matrix.one_apply, qftMatrix, Matrix.of_apply]
  have hsum : ∀ l : Fin N,
      star ((Real.sqrt N : ℂ)⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) *
        ((Real.sqrt N : ℂ)⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (k : ℕ) / N))
        = ((N : ℂ))⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N) := by
    intro l
    have hstar : star ((Real.sqrt N : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N))
        = (Real.sqrt N : ℂ)⁻¹ *
          Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) := by
      rw [Complex.star_def, map_mul, ← Complex.exp_conj]
      congr 1
      · simp
      · congr 1
        simp [Complex.ext_iff]
        ring
    rw [hstar]
    rw [show (Real.sqrt N : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) *
        ((Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (k : ℕ) / N))
        = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) *
          (Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) *
            Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (k : ℕ) / N)) from by ring]
    rw [hsq, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun l _ => hsum l)]
  rw [← Finset.mul_sum]
  rw [show ∑ l : Fin N, Complex.exp
        (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N)
      = ∑ l ∈ Finset.range N, Complex.exp
        (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N) from by
    rw [Finset.sum_range fun l => Complex.exp
        (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N)]]
  rw [sum_root_of_unity N hN ((k : ℤ) - (j : ℤ))]
  have hiff : ((N : ℤ) ∣ ((k : ℤ) - (j : ℤ))) ↔ j = k := by
    constructor
    · intro h
      have hj : (j : ℤ) < N := by exact_mod_cast j.isLt
      have hk : (k : ℤ) < N := by exact_mod_cast k.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℕ) := Int.natCast_nonneg _
      have hk0 : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
      have hzero : (k : ℤ) - (j : ℤ) = 0 := by
        rcases h with ⟨c, hc⟩
        have hc1 : c = 0 := by nlinarith [hc]
        simp [hc1] at hc
        exact hc
      have : (j : ℕ) = (k : ℕ) := by omega
      exact Fin.ext this
    · intro h
      simp [h]
  by_cases h : j = k
  · simp [h, hNC]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh)), mul_zero]

/-- **The 7-qubit QFT matrix is unitary.** -/
