import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `2^n`-th root of unity used by the quantum Fourier transform. -/

lemma sum_pow_of_pow_eq_one {N : ℕ} {z : ℂ} (hz : z ^ N = 1) :
    ∑ k ∈ Finset.range N, z ^ k = if z = 1 then (N : ℂ) else 0 := by
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz, sub_self, zero_div]

/-- The key orthogonality relation for the rows of the QFT matrix. -/
