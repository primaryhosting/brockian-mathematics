import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma adjMatrix_mul_dftMatrix {N : ℕ} :
    (SimpleGraph.cycleGraph (N + 3)).adjMatrix ℂ * dftMatrix (N + 3)
      = dftMatrix (N + 3) * huckelDiag (N + 3) := by
  have hn : (N + 3) ≠ 0 := by omega
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (pred_ne_succ j), huckelDiag, Matrix.mul_diagonal]
  set z : ℂ := zeta (N + 3) ^ ((j : ℕ) * (k : ℕ)) with hz
  set c : ℂ := zeta (N + 3) ^ (k : ℕ) with hc
  have hcne : c ≠ 0 := pow_ne_zero _ (zeta_ne_zero _)
  have hsucc : dftMatrix (N + 3) (j + 1) k = z * c := by
    rw [dftMatrix_apply, hz, hc, ← pow_add]
    exact zeta_pow_modEq hn
      (((succ_val_modEq (N := N + 1) j).mul_right (k : ℕ)).trans (by rw [add_mul, one_mul]))
  have hpred : dftMatrix (N + 3) (j - 1) k = z * c⁻¹ := by
    have hmul : dftMatrix (N + 3) (j - 1) k * c = z := by
      rw [dftMatrix_apply, hz, hc, ← pow_add]
      refine zeta_pow_modEq hn ?_
      simpa [add_mul] using (pred_val_modEq (N := N + 1) j).mul_right (k : ℕ)
    rw [← hmul]
    field_simp
  rw [hpred, hsucc, dftMatrix_apply, ← hz]
  rw [← zeta_pow_add_inv hn (k : ℕ), ← hc]
  ring

/-- **Hückel cycle spectrum.**  The adjacency (Hückel) eigenvalues of the cycle graph `Cₙ`
(`n ≥ 3`) are exactly the numbers `2 cos (2πk/n)` for `k = 0, …, n-1`. -/
