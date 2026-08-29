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

theorem dftU_mul_dftV : dftU * dftV = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 14, dftU i k * dftV k j = (14 : ℂ)⁻¹ * chi ((i - j) * k) := by
    intro k
    show chi (i * k) * ((14 : ℂ)⁻¹ * chi (-(k * j))) = _
    rw [show ((i - j) * k : ZMod 14) = i * k + (-(k * j)) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, chi_sum]
  by_cases hij : i = j
  · subst hij; norm_num
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

