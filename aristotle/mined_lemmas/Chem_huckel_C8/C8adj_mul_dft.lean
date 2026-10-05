import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma C8adj_mul_dft : C8adj * C8dft = C8dft * Matrix.diagonal C8eigen := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [C8adj_sum i (fun l => C8dft l j)]
  simp only [C8dft, Matrix.vandermonde_apply, C8eigen_eq]
  have key : ∀ m : ℕ, (zeta8 ^ m) ^ (j : ℕ) = (zeta8 ^ (j : ℕ)) ^ m := by
    intro m
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [key, key, key]
  exact pow_cycle_ident _ (by rw [← pow_mul, Nat.mul_comm, pow_mul, zeta8_pow_eight, one_pow]) i

