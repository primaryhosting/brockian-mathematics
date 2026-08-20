import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma A13_mul_P13 : A13 * P13 = P13 * D13 := by
  have hne : ∀ i : Fin 13, i - 1 ≠ i + 1 := by decide
  ext j k
  have hcol : (A13 * P13) j k = ∑ l ∈ (SimpleGraph.cycleGraph 13).neighborFinset j, P13 l k := by
    have h := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 13) j
      (fun l => P13 l k)
    simpa [A13, Matrix.mul_apply, Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
      ite_mul] using h
  have hw : (qc k) ^ 13 = 1 := qc_pow_13 k
  have hw0 : qc k ≠ 0 := qc_ne_zero k
  have h1 : (qc k) ^ ((1 : Fin 13)).val = qc k := by norm_num
  have hminus : (qc k) ^ ((j - 1 : Fin 13)).val = (qc k) ^ (j : ℕ) * (qc k)⁻¹ := by
    have h2 := pow_val_add hw (j - 1) 1
    rw [sub_add_cancel, h1] at h2
    field_simp
    linear_combination -h2
  have hplus : (qc k) ^ ((j + 1 : Fin 13)).val = (qc k) ^ (j : ℕ) * qc k := by
    have h2 := pow_val_add hw j 1
    rwa [h1] at h2
  rw [hcol, neighborFinset_cycle13, Finset.sum_pair (hne j), P13_apply, P13_apply, D13,
    Matrix.mul_diagonal, P13_apply, hminus, hplus, ← qc_add_qc_inv k]
  ring

