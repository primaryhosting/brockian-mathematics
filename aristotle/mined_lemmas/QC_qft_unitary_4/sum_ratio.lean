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

lemma sum_ratio (k l : Fin 16) :
    ∑ j : Fin 16, (omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹) ^ (j : ℕ)
      = if k = l then (16 : ℂ) else 0 := by
  set z : ℂ := omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹ with hz
  rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) 16]
  by_cases h : k = l
  · subst h
    have hz1 : z = 1 := (ratio_eq_one_iff k k).2 rfl
    simp [hz1]
  · have hz1 : z ≠ 1 := fun hc => h ((ratio_eq_one_iff k l).1 hc)
    rw [geom_sum_eq hz1, ratio_pow_16 k l]
    simp [h]

/-- **The 4-qubit quantum Fourier transform matrix is unitary.** -/
