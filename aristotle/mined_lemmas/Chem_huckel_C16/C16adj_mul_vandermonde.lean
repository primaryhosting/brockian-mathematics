/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma C16adj_mul_vandermonde :
    C16adj * Matrix.vandermonde node16
      = Matrix.vandermonde node16 * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ)) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal,
    sum_over_neighbors i (fun j => (Matrix.vandermonde node16) j k)]
  simp only [vandermonde_apply_eq]
  set x : ℂ := node16 k with hxdef
  have hx16 : x ^ 16 = 1 := node16_pow_16 k
  have h1 : x ^ ((i - 1 : Fin 16) : ℕ) = x ^ (i : ℕ) * x ^ 15 := by
    rw [sub_eq_add_neg, pow_val_add hx16 i (-1)]
    norm_num
  have h2 : x ^ ((i + 1 : Fin 16) : ℕ) = x ^ (i : ℕ) * x := by
    rw [pow_val_add hx16 i 1]
    norm_num
  rw [h1, h2, ← node16_add_inv k, ← hxdef]
  ring

