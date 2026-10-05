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

lemma pow_val_add (w : ℂ) (hw : w ^ 15 = 1) (a b : Fin 15) :
    w ^ ((a + b : Fin 15) : ℕ) = w ^ (a : ℕ) * w ^ (b : ℕ) := by
  have hmod : ∀ x : ℕ, w ^ (x % 15) = w ^ x := by
    intro x
    conv_rhs => rw [← Nat.div_add_mod x 15]
    rw [pow_add, pow_mul, hw, one_pow, one_mul]
  rw [Fin.val_add, hmod, pow_add]

/-- The columns of the Fourier matrix are eigenvectors of the adjacency matrix. -/
