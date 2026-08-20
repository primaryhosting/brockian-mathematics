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

lemma shift12_pow_12 : shift12 ^ 12 = 1 := by
  have h : (12 : ZMod 12) = 0 := by decide
  rw [shift12_pow]
  ext i j
  simp [Matrix.one_apply, eq_comm, h]

