import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` (the Hückel spectrum of a
15-membered annulene, in units of β above α) are exactly the numbers `2 cos (2πk/15)`
for `k = 0, …, 14`.

The proof writes the adjacency matrix as `S + S¹⁴`, where `S` is the cyclic shift permutation
matrix, identifies the spectrum of `S` with the set of 15-th roots of unity, and then applies
the polynomial spectral mapping theorem over `ℂ`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The cyclic shift permutation matrix on `Fin 15`: `shift i j = 1` iff `i - 1 = j`. -/

lemma exp_pow_fifteen : (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ 15 = 1 := by
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [show (15 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 15) = 2 * (Real.pi : ℂ) * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

/-- For `ν = exp (2πik/15)` one has `ν + ν¹⁴ = ν + ν⁻¹ = 2 cos (2πk/15)`. -/
