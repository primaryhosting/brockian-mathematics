/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem C18mat_mul_Pmat : C18mat * Pmat = Pmat * Dmat := by
  ext j k
  have lhs : (C18mat * Pmat) j k = wch ((j - 1) * k) + wch ((j + 1) * k) := by
    simp only [Matrix.mul_apply, C18mat, Matrix.circulant_apply, Pmat]
    exact sum_two_terms (fun l => wch (l * k)) j
  have rhs : (Pmat * Dmat) j k = wch (j * k) * hval k := by
    simp [Matrix.mul_apply, Dmat, Pmat, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [lhs, rhs, ← wch_add_wch_neg k]
  have h1 : (j - 1) * k = j * k + (-k) := by ring
  have h2 : (j + 1) * k = j * k + k := by ring
  rw [h1, h2, wch_add, wch_add]
  ring

