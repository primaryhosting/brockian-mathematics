/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for `C₉`

The Hückel matrix of the cycle `C₉` (in units where the Coulomb integral is `0` and the
resonance integral is `1`) is the adjacency matrix of `SimpleGraph.cycleGraph 9`.
This file diagonalizes it by the discrete Fourier transform (a Vandermonde matrix built from
a primitive ninth root of unity) and computes its characteristic polynomial and spectrum:
the eigenvalues are `2 cos (2πk/9)`, `k = 0, …, 8`.
-/

open Matrix Polynomial SimpleGraph

namespace Chem

/-- A primitive ninth root of unity. -/

lemma lam_eq (k : Fin 9) : lam k = zeta ^ (k : ℕ) + zeta ^ (8 * (k : ℕ)) := by
  have h1 : zeta ^ (8 * (k : ℕ)) * zeta ^ (k : ℕ) = 1 := by
    rw [← pow_add]
    have h : 8 * (k : ℕ) + (k : ℕ) = 9 * (k : ℕ) := by ring
    rw [h, pow_mul, zeta_pow_nine, one_pow]
  have h2 : zeta ^ (8 * (k : ℕ)) = (zeta ^ (k : ℕ))⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2, zeta_pow_eq_exp, ← Complex.exp_neg, lam, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

