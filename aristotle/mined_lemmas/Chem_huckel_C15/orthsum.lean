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

lemma orthsum (a b : Fin 15) :
    ∑ k : Fin 15, ((zeta ^ (a : ℕ)) * (zeta ^ (b : ℕ))⁻¹) ^ (k : ℕ) =
      if a = b then 15 else 0 := by
  have hz : ((zeta ^ (a : ℕ)) * (zeta ^ (b : ℕ))⁻¹) ^ 15 = 1 := by
    rw [mul_pow, inv_pow, zeta_pow_pow_15, zeta_pow_pow_15, inv_one, mul_one]
  rw [geom15 _ hz]
  congr 1
  simp only [eq_iff_iff]
  rw [mul_inv_eq_one₀ (pow_ne_zero _ zeta_ne_zero)]
  constructor
  · intro h
    exact Fin.ext (isPrimitiveRoot_zeta.pow_inj a.isLt b.isLt h)
  · rintro rfl
    rfl

