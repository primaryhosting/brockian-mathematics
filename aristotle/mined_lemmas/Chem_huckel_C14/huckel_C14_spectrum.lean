/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C₁₄` is diagonalised by the discrete Fourier
transform on `ZMod 14`; its characteristic polynomial is therefore
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, i.e. its eigenvalues are `2 cos (2πk/14)` for `k = 0, …, 13`.
-/

open Complex Polynomial Matrix

namespace Chem

noncomputable section

/-- A primitive 14-th root of unity. -/

theorem huckel_C14_spectrum (mu : ℂ) :
    adjC14.charpoly.IsRoot mu ↔
      ∃ k : ℕ, k < 14 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ) := by
  rw [Polynomial.IsRoot, huckel_C14, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h
    exact ⟨k, Finset.mem_range.mp hk, h⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr hk, by simp⟩

/-- The same statement for Mathlib's cycle graph `C₁₄`: the characteristic polynomial of its
adjacency matrix is `∏_{k=0}^{13} (X - 2 cos (2πk/14))`. -/
