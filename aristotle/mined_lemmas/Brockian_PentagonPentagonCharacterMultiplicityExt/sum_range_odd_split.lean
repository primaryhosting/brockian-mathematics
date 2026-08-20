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

lemma sum_range_odd_split (m : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ Finset.range (2 * m + 1), F k
      = F 0 + ∑ j ∈ Finset.Icc 1 m, (F j + F (2 * m + 1 - j)) := by
  have hsplit : ∑ k ∈ Finset.range (2 * m + 1), F k
      = (∑ k ∈ Finset.Ico 0 (m + 1), F k) + ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), F k := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive] <;> omega
  have h1 : ∑ k ∈ Finset.Ico 0 (m + 1), F k = F 0 + ∑ j ∈ Finset.Icc 1 m, F j := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    congr 1
  have h2 : ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), F k
      = ∑ j ∈ Finset.Icc 1 m, F (2 * m + 1 - j) := by
    apply Finset.sum_nbij' (i := fun k => 2 * m + 1 - k) (j := fun k => 2 * m + 1 - k) <;>
      intro a ha <;> simp only [Finset.mem_Ico, Finset.mem_Icc] at * <;> try omega
    congr 1
    omega
  rw [hsplit, h1, h2, Finset.sum_add_distrib]
  ring

/-- **Decomposition of the vertex representation of an odd `n`-gon.**
For `n = 2m+1`, the permutation character of the action of `DihedralGroup n` on the vertices
is the sum of the trivial character and the `m` two-dimensional characters
`rotChar n 1, …, rotChar n m`. In particular the vertex representation has dimension
`n = 1 + 2m`. -/
