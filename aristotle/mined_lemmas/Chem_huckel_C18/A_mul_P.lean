import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma A_mul_P : A * P = P * Matrix.diagonal mu := by
  ext i j
  have hne : (i - 1 : Fin 18) ≠ i + 1 := by
    intro h
    simp [Fin.ext_iff, Fin.sub_def, Fin.add_def] at h
    omega
  have hsum : (A * P) i j = P (i - 1) j + P (i + 1) j := by
    rw [Matrix.mul_apply]
    have hs : ∑ l, A i l * P l j
        = ∑ l ∈ (SimpleGraph.cycleGraph 18).neighborFinset i, P l j := by
      rw [A, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
      simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
    rw [hs]
    have hnb : (SimpleGraph.cycleGraph 18).neighborFinset i = {i - 1, i + 1} := by
      have := @SimpleGraph.cycleGraph_neighborFinset 16 i
      simpa using this
    rw [hnb, Finset.sum_pair hne]
  rw [hsum, Matrix.mul_apply, Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply_eq]
    rw [P_apply, P_apply, P_apply]
    rw [mul_comm (i : ℕ) (j : ℕ), mul_comm ((i - 1 : Fin 18) : ℕ) (j : ℕ),
      mul_comm ((i + 1 : Fin 18) : ℕ) (j : ℕ), pow_mul, pow_mul, pow_mul]
    have hx : (zeta ^ (j : ℕ)) ^ 18 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_18, one_pow]
    rw [pow_pred_fin _ hx, pow_succ_fin _ hx, ← zeta_pow_add_inv j]
    ring
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Hückel theory for C₁₈.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₈` is `∏ k, (X - 2 cos (2πk/18))`, i.e. the adjacency eigenvalues of `C₁₈`
(with multiplicity) are exactly `2 cos (2πk/18)` for `k = 0, …, 17`. -/
