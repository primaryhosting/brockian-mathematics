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

lemma zeta_pow_add_inv (k : Fin 15) :
    zeta ^ (k : ℕ) + (zeta ^ (k : ℕ))⁻¹ = hueckelEval k := by
  have hzk : zeta ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hzk, ← Complex.exp_neg, hueckelEval, Complex.ofReal_cos, Complex.cos, neg_mul]
  ring

/-- Periodicity: for a 15-th root of unity `w`, the map `a ↦ w ^ a.val` is a
homomorphism from `Fin 15`. -/
