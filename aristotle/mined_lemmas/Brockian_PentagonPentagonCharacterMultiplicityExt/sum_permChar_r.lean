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

lemma sum_permChar_r [NeZero n] : ∑ i : ZMod n, permChar n (r i) = (n : ℝ) := by
  rw [Finset.sum_eq_single (0 : ZMod n)]
  · exact permChar_r_zero
  · intro b _ hb; exact permChar_r_of_ne_zero hb
  · intro h; exact absurd (Finset.mem_univ _) h

