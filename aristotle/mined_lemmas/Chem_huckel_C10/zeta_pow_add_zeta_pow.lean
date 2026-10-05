/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/

lemma zeta_pow_add_zeta_pow (m : ℕ) (hm : m ≤ 10) :
    zeta ^ m + zeta ^ (10 - m) = 2 * (Real.cos (2 * Real.pi * m / 10) : ℝ) := by
  have h1 : zeta ^ m = Complex.exp ((2 * Real.pi * m / 10 : ℝ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hmul : zeta ^ m * zeta ^ (10 - m) = 1 := by
    rw [← pow_add, show m + (10 - m) = 10 by omega, zeta_pow_ten]
  have h2 : zeta ^ (10 - m) = Complex.exp (-((2 * Real.pi * m / 10 : ℝ) * Complex.I)) := by
    rw [Complex.exp_neg, ← h1]
    exact (DivisionMonoid.inv_eq_of_mul _ _ hmul).symm
  rw [h1, h2, Complex.ofReal_cos, Complex.two_cos, neg_mul]

/-- The (unnormalised) discrete Fourier matrix `U j k = ζ^{jk}`; it is a Vandermonde matrix in the
nodes `ζ^j`. -/
