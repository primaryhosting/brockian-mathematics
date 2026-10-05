/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Hückel (tight-binding) spectrum of the annulene `C₁₅`: the eigenvalues of the
adjacency matrix of the cycle graph `C₁₅` are exactly `2 cos (2πk/15)`, `k = 0, …, 14`.

Mathlib has the cycle graph (`SimpleGraph.cycleGraph`) and its adjacency matrix
(`SimpleGraph.adjMatrix`), the spectrum of a diagonal matrix (`spectrum_diagonal`) and
invariance of the spectrum under conjugation (`spectrum.units_conjugate`), but no
diagonalization of circulant matrices, so we build the discrete Fourier transform
matrix explicitly.
-/

namespace Chem

open Complex Matrix SimpleGraph

noncomputable section

/-- A primitive 15-th root of unity. -/

lemma adj_mul_Pmat :
    (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 15)) * Pmat
      = Pmat * Matrix.diagonal hueckelEval := by
  ext i k
  rw [SimpleGraph.adjMatrix_mul_apply, Matrix.mul_diagonal]
  have hnb : (SimpleGraph.cycleGraph 15).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset
  have hne : ∀ m : Fin 15, m - 1 ≠ m + 1 := by decide
  rw [hnb, Finset.sum_pair (hne i)]
  set w : ℂ := zeta ^ (k : ℕ) with hwdef
  have hw15 : w ^ 15 = 1 := by rw [hwdef]; exact zeta_pow_pow_15 _
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw15; norm_num at hw15
  have hval : ∀ m : Fin 15, Pmat m k = w ^ (m : ℕ) := by
    intro m
    simp only [Pmat, Matrix.of_apply, hwdef, ← pow_mul, mul_comm]
  have hone : ((1 : Fin 15) : ℕ) = 1 := rfl
  have hplus : Pmat (i + 1) k = w ^ (i : ℕ) * w := by
    rw [hval, pow_val_add w hw15, hone, pow_one]
  have hminus : Pmat (i - 1) k = w ^ (i : ℕ) * w⁻¹ := by
    have h1 : (i - 1) + 1 = i := sub_add_cancel i 1
    have h2 := pow_val_add w hw15 (i - 1) 1
    rw [h1, hone, pow_one] at h2
    rw [hval, h2]
    field_simp
  rw [hplus, hminus, hval, ← zeta_pow_add_inv k, ← hwdef]
  ring

/-- **Hückel theory for C₁₅.** The adjacency eigenvalues of the cycle graph `C₁₅`
are exactly `2 cos (2πk/15)` for `k = 0, …, 14`. -/
