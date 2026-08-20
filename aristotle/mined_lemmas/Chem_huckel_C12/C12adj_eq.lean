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

lemma C12adj_eq : C12adj = shift12 + shift12 ^ 11 := by
  have key : ∀ i : ZMod 12, i + 1 ≠ i - 1 := by decide
  ext i j
  have h11 : ((11 : ℕ) : ZMod 12) = -1 := by decide
  rw [shift12_pow]
  simp only [C12adj, shift12, Matrix.of_apply, Matrix.add_apply, h11, ← sub_eq_add_neg]
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
    simp [h1, h2, key i, Ne.symm (key i)]

/-- The spectrum of the cyclic shift matrix consists exactly of the `12`-th roots of unity. -/
