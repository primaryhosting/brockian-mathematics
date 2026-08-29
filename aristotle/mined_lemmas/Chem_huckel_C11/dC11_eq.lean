/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as an ordinary block comment with identical text.)

import Mathlib

/-!
# Huckel C 11

The adjacency eigenvalues of the cycle graph `C₁₁` are `2·cos(2πk/11)` for `k = 0, …, 10`.

The proof diagonalizes the adjacency matrix `A` of `SimpleGraph.cycleGraph 11` by the
discrete Fourier (Vandermonde) matrix `U j k = ω^{jk}`, where `ω = exp(2πi/11)`:
`A * U = U * diagonal d` with `d k = ω^k + ω^{-k} = 2 cos (2πk/11)`.
Since `det U ≠ 0` (`Matrix.det_vandermonde_ne_zero_iff`, `ω` being a primitive root),
`det (A - z) = ∏ k (d k - z)`, and `Matrix.exists_mulVec_eq_zero_iff` converts this into
the statement about eigenvalues.
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 11-th root of unity. -/

theorem dC11_eq (k : Fin 11) :
    dC11 k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) := by
  have hprod : om ^ (k : ℕ) * om ^ (10 * (k : ℕ)) = 1 := by
    rw [← pow_add]
    have : (k : ℕ) + 10 * (k : ℕ) = 11 * (k : ℕ) := by ring
    rw [this, pow_mul, om_pow_eleven, one_pow]
  have hinv : om ^ (10 * (k : ℕ)) = (om ^ (k : ℕ))⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [mul_comm] at hprod; rw [mul_comm]; exact hprod)
  rw [dC11, hinv, om_pow_eq_exp, ← Complex.exp_neg, Complex.exp_mul_I, ← neg_mul,
    Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

