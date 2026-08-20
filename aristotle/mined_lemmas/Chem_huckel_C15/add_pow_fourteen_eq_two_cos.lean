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

lemma add_pow_fourteen_eq_two_cos (k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k
        + ((Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k) ^ 14
      = ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ) := by
  set θ : ℂ := ((2 * Real.pi * k / 15 : ℝ) : ℂ) with hθ
  have hw : (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k = Complex.exp (θ * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hne : (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k ≠ 0 := by
    simp [Complex.exp_ne_zero]
  have h14 : ((Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k) ^ 14
      = ((Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k)⁻¹ := by
    field_simp
    rw [← pow_mul, mul_comm k 15, pow_mul, exp_pow_fifteen, one_pow]
  rw [h14, hw, ← Complex.exp_neg, ← neg_mul, ← Complex.two_cos, hθ]
  push_cast
  ring

/-- **Hückel spectrum of `C₁₅`.**  The eigenvalues of the adjacency matrix of the cycle graph
`C₁₅` are exactly the numbers `2 cos (2πk/15)` for `k = 0, …, 14`. -/
