/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₉`

We show that the spectrum of the adjacency matrix of the cycle graph `C₁₉`
(the Hückel matrix of the annulene `C₁₉` in units where `α = 0`, `β = 1`)
is exactly `{2 cos (2πk/19) : k = 0, …, 18}`.

The proof diagonalizes the circulant adjacency matrix by the discrete Fourier matrix.
-/

namespace Chem

open Complex Matrix Finset

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- A primitive 19-th root of unity. -/

lemma C19adj_mul_Fm : C19adj * Fm = Fm * diagonal mu := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 19, C19adj i k * Fm k j
      = (if k = i + 1 then ee (k * j) else 0) + (if k = i - 1 then ee (k * j) else 0) := by
    intro k
    rw [C19adj_apply]
    simp only [Fm, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun k => ee (k * j)),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun k => ee (k * j))]
  simp only [Finset.mem_univ, if_true]
  rw [Matrix.mul_diagonal]
  rw [show (i + 1) * j = i * j + j by ring, show (i - 1) * j = i * j + (-j) by ring,
    ee_add, ee_add, ← mul_add, ee_add_ee_neg]
  rfl

