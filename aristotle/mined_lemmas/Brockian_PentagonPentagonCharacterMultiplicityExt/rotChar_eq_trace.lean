import RequestProject.PentagonExt

/-!
# Decomposition of the vertex representation of a regular `n`-gon, `n` odd

For an odd number of vertices `n = 2m+1`, the permutation character of `DihedralGroup n`
acting on the vertices of the regular `n`-gon decomposes as the trivial character plus the
`m` two-dimensional characters `rotChar n 1, …, rotChar n m`.

For `n = 5` this is the classical pentagon statement `5 = 1 + 2 + 2`.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- For an odd `n`-gon every reflection fixes exactly one vertex. -/

lemma rotChar_eq_trace (n : ℕ) [NeZero n] (j : ℕ) (g : DihedralGroup n) :
    ((rotChar n j g : ℝ) : ℂ) = Matrix.trace (twoDimRep n j g) := by
  cases g with
  | r i =>
    show ((2 * Real.cos (2 * Real.pi * j * i.val / n) : ℝ) : ℂ) =
      Matrix.trace !![rootPow n j i, 0; 0, rootPow n j (-i)]
    rw [Matrix.trace_fin_two_of]
    have hi : rootPow n j (-i) = (rootPow n j i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact rootPow_mul_neg n j i)
    rw [rootPow_eq_exp, hi, rootPow_eq_exp, ← Complex.exp_neg]
    push_cast
    rw [Complex.cos]
    ring_nf
  | sr i =>
    show ((0 : ℝ) : ℂ) = Matrix.trace !![0, rootPow n j (-i); rootPow n j i, 0]
    rw [Matrix.trace_fin_two_of]
    norm_num

/-!
### The pentagon case
-/

/-- The pentagon (`n = 5`) case of the main theorem: in the permutation representation on the
five vertices, the trivial character occurs with multiplicity `1`, the sign character with
multiplicity `0`, and each two-dimensional character with multiplicity `1`. -/
