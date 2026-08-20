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

lemma sum_pow_stdAddChar [NeZero n] (i : ZMod n) :
    ∑ k ∈ Finset.range n, (ZMod.stdAddChar i) ^ k = if i = 0 then (n : ℂ) else 0 := by
  by_cases h : i = 0
  · subst h; simp
  · rw [if_neg h]
    have hne : (ZMod.stdAddChar i : ℂ) ≠ 1 := fun hc =>
      h (ZMod.injective_stdAddChar (by rw [hc]; simp))
    have hpow : (ZMod.stdAddChar i : ℂ) ^ n = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, show (n : ℕ) • i = 0 by simp [nsmul_eq_mul],
        AddChar.map_zero_eq_one]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Splitting a sum over `range (2m+1)` into the zero term and the pairs `{j, n - j}`. -/
