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

lemma shift12_pow (n : ℕ) :
    shift12 ^ n = Matrix.of fun i j => if j = i + (n : ZMod 12) then 1 else 0 := by
  induction n with
  | zero => ext i j; simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
      ext i j
      rw [pow_succ, Matrix.mul_apply, ih]
      simp only [Matrix.of_apply, shift12, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      push_cast
      rw [add_assoc]

