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

lemma permChar_r_zero [NeZero n] : permChar n (r 0) = (n : ℝ) := by
  have h : fixedVertices n (r (0 : ZMod n)) = Finset.univ :=
    Finset.filter_true_of_mem (fun x _ => sub_zero x)
  rw [permChar, h, Finset.card_univ, ZMod.card]

