import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₂`

We show that the eigenvalues (i.e. the spectrum) of the adjacency matrix of the cycle graph
`C₁₂`, viewed as a complex matrix indexed by `ZMod 12`, are exactly the numbers
`2 * cos (2 * π * k / 12)` for `k = 0, …, 11`.

The proof goes through the cyclic shift matrix `S` on `ZMod 12`: the adjacency matrix is
`S + S ^ 11`, the spectrum of `S` is the set of `12`-th roots of unity, and the polynomial
spectral mapping theorem over `ℂ` transports this to the adjacency matrix.
-/

namespace Chem

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod 12`. -/

lemma exp_add_pow_eleven (k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * k / 12)
        + (Complex.exp (2 * Real.pi * Complex.I * k / 12)) ^ 11
      = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / 12 with hθ
  have hz : Complex.exp (2 * Real.pi * Complex.I * k / 12)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hθ]; push_cast; ring_nf
  have h11 : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 11 = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_nat_mul,
      show ((11 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)
          = -((θ : ℂ) * Complex.I) + (k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) from by
        rw [hθ]; push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hz, h11]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- **Hückel theory for the 12-cycle**: the adjacency eigenvalues of the cycle graph `C₁₂`
are `2 cos (2πk/12)` for `k = 0, …, 11`. -/
