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

lemma sum_root_of_unity (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ l ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (m * l) / N)
      = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * m / N) with hz
  have hterm : ∀ l : ℕ, Complex.exp (2 * Real.pi * Complex.I * (m * l) / N) = z ^ l := by
    intro l
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  by_cases hdvd : (N : ℤ) ∣ m
  · have hz1 : z = 1 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hz, Complex.exp_eq_one_iff]
      refine ⟨c, ?_⟩
      rw [hc]
      push_cast
      field_simp
    simp [hz1, hdvd]
  · have hzN : z ^ N = 1 := by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      field_simp
    have hz1 : z ≠ 1 := by
      intro h
      rw [hz, Complex.exp_eq_one_iff] at h
      obtain ⟨c, hc⟩ := h
      apply hdvd
      refine ⟨c, ?_⟩
      field_simp at hc
      exact_mod_cast hc
    rw [geom_sum_eq hz1, hzN, sub_self, zero_div]
    simp [hdvd]

/-- The `N × N` QFT matrix is unitary, for any `N > 0`. -/
