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

lemma rotChar_r_eq_rootPow [NeZero n] (i : ZMod n) (j : ℕ) (hj : j ≤ n) :
    ((rotChar n j (r i) : ℝ) : ℂ) =
      (ZMod.stdAddChar i) ^ j + (ZMod.stdAddChar i) ^ (n - j) := by
  have hpow : (ZMod.stdAddChar i : ℂ) ^ j = rootPow n j i := by
    rw [← AddChar.map_nsmul_eq_pow, rootPow]
    congr 1
    simp [nsmul_eq_mul]
  have hn : (ZMod.stdAddChar i : ℂ) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, show (n : ℕ) • i = 0 by simp [nsmul_eq_mul],
      AddChar.map_zero_eq_one]
  have hsplit : (ZMod.stdAddChar i : ℂ) ^ (n - j) * (ZMod.stdAddChar i : ℂ) ^ j = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, hn]
  have hinv : (ZMod.stdAddChar i : ℂ) ^ (n - j) = (rootPow n j i)⁻¹ := by
    rw [← hpow]
    exact eq_inv_of_mul_eq_one_left hsplit
  have htrace := rotChar_eq_trace n j (r i)
  rw [htrace]
  show Matrix.trace !![rootPow n j i, 0; 0, rootPow n j (-i)] = _
  rw [Matrix.trace_fin_two_of, hpow, hinv]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact rootPow_mul_neg n j i)

/-- The full sum of the powers of the root of unity attached to `i : ZMod n`. -/
