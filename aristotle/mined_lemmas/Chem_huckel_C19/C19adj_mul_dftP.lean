/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma C19adj_mul_dftP :
    C19adj * dftP = dftP * diagonal (fun k : Fin 19 => huckelEigenvalue k.val) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hsub : j - 1 = j + 18 := by revert j; decide
  have hne : (j + 1) ≠ (j - 1) := by revert j; decide
  have hterm : ∀ i : Fin 19, C19adj j i * dftP i k
      = if i ∈ ({j + 1, j - 1} : Finset (Fin 19)) then dftP i k else 0 := by
    intro i
    simp only [C19adj, SimpleGraph.adjMatrix_apply, Finset.mem_insert, Finset.mem_singleton]
    by_cases h : (cycleGraph 19).Adj j i
    · rw [if_pos h, one_mul, if_pos ((cycle19_adj_iff j i).1 h)]
    · rw [if_neg h, zero_mul, if_neg (fun hc => h ((cycle19_adj_iff j i).2 hc))]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]
  -- now compute the two Fourier entries
  have e1 : dftP (j + 1) k = zeta ^ (j.val * k.val) * zeta ^ k.val := by
    have hval : (j + 1).val = (j.val + 1) % 19 := rfl
    calc dftP (j + 1) k = zeta ^ (((j.val + 1) % 19) * k.val) := by rw [dftP, hval]
      _ = zeta ^ ((j.val + 1) * k.val) := by
          exact zeta_pow_congr (Nat.ModEq.mul_right k.val (Nat.mod_mod_of_dvd _ dvd_rfl))
      _ = zeta ^ (j.val * k.val) * zeta ^ k.val := by rw [add_mul, one_mul, pow_add]
  have e2 : dftP (j - 1) k = zeta ^ (j.val * k.val) * (zeta ^ k.val)⁻¹ := by
    have hj : j - 1 = j + 18 := hsub
    have hval : (j + 18).val = (j.val + 18) % 19 := rfl
    have hinv : zeta ^ (18 * k.val) = (zeta ^ k.val)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_add]
      have h19 : 18 * k.val + k.val = 19 * k.val := by ring
      rw [h19, pow_mul, zeta_pow_19, one_pow]
    calc dftP (j - 1) k = zeta ^ (((j.val + 18) % 19) * k.val) := by rw [hj, dftP, hval]
      _ = zeta ^ ((j.val + 18) * k.val) := by
          exact zeta_pow_congr (Nat.ModEq.mul_right k.val (Nat.mod_mod_of_dvd _ dvd_rfl))
      _ = zeta ^ (j.val * k.val) * (zeta ^ k.val)⁻¹ := by
          rw [add_mul, pow_add, hinv]
  rw [e1, e2, ← mul_add, zeta_pow_add_inv k.val, dftP]

/-- **Hückel theory for C₁₉.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₉` factors as `∏_{k=0}^{18} (X - 2 cos (2πk/19))`; that is, the adjacency
eigenvalues of `C₁₉` are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
