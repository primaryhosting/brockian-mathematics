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

theorem adj_mul_dftU : adjC14 * dftU = dftU * eigD := by
  ext i k
  have hne : (i - 1 : ZMod 14) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 14) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hR : (dftU * eigD) i k = dftU i k * ((2 * Real.cos (theta k.val) : ℝ) : ℂ) :=
    Matrix.mul_diagonal _ _ _ _
  rw [Matrix.mul_apply, hR]
  have key : ∀ j : ZMod 14, adjC14 i j * dftU j k
      = (if j = i - 1 then chi (j * k) else 0) + (if j = i + 1 then chi (j * k) else 0) := by
    intro j
    by_cases h1 : j = i - 1
    · subst h1
      simp [adjC14, dftU, sub_sub_cancel, hne]
    · by_cases h2 : j = i + 1
      · subst h2
        simp [adjC14, dftU, h1, add_sub_cancel_left]
      · have h3 : ¬ (i - j = 1 ∨ j - i = 1) := by
          rintro (h | h)
          · exact h1 (by linear_combination -h)
          · exact h2 (by linear_combination h)
        simp [adjC14, dftU, h1, h2, h3]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => chi (j * k)),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => chi (j * k))]
  simp only [Finset.mem_univ, if_true]
  have e1 : ((i - 1) * k : ZMod 14) = i * k + (-k) := by ring
  have e2 : ((i + 1) * k : ZMod 14) = i * k + k := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  show chi (i * k) * chi (-k) + chi (i * k) * chi k = chi (i * k) * _
  rw [← mul_add, add_comm (chi (-k)) (chi k), chi_add_chi_neg]

/-- Orthogonality of characters on `ZMod 14`. -/
