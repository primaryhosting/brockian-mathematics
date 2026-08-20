/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma adj_mul_vec : C19adj * C19vec = C19vec * Matrix.diagonal C19eig := by
  ext i k
  have h1 : (C19adj * C19vec) i k = om ^ ((i + 1).val * k.val) + om ^ ((i - 1).val * k.val) := by
    simp [Matrix.mul_apply, C19adj, C19vec, add_mul, Finset.sum_add_distrib]
  have e1 : i + 1 = i + ((1 : ℕ) : ZMod 19) := by norm_num
  have e2 : i - 1 = i + ((18 : ℕ) : ZMod 19) := by
    rw [sub_eq_add_neg]
    norm_num
    decide
  rw [h1, e1, e2, om_shift, om_shift, Matrix.mul_diagonal]
  show om ^ ((i.val + 1) * k.val) + om ^ ((i.val + 18) * k.val)
      = om ^ (i.val * k.val) * C19eig k
  rw [C19eig, ← om_pow_add k.val, add_mul, add_mul, pow_add, pow_add, mul_add]
  ring_nf

/-- The Fourier matrix is invertible: `V · V̄ = 19 · I`. -/
