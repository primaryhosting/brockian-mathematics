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

lemma conj_qftRoot (n : ℕ) : (starRingEnd ℂ) (qftRoot n) = (qftRoot n)⁻¹ := by
  rw [qftRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_pow, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The entries of the QFT matrix, written as powers of the root of unity. -/
