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

lemma sum_permChar_sr [NeZero n] : ∑ i : ZMod n, permChar n (sr i) = (n : ℝ) := by
  classical
  have key : ∑ i : ZMod n, (fixedVertices n (sr i)).card = Fintype.card (ZMod n) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun x : ZMod n => x + x) (s := (Finset.univ : Finset (ZMod n)))
      (t := (Finset.univ : Finset (ZMod n))) (fun x _ => Finset.mem_univ _)
    have hfe : ∀ i : ZMod n,
        (Finset.univ.filter fun x : ZMod n => x + x = i) = fixedVertices n (sr i) := by
      intro i
      ext x
      simp only [fixedVertices, Finset.mem_filter, Finset.mem_univ, true_and, ngonAct_sr]
      constructor
      · intro h; linear_combination -h
      · intro h; linear_combination -h
    simp only [hfe] at hfib
    rw [← hfib, Finset.card_univ]
  calc ∑ i : ZMod n, permChar n (sr i)
      = ((∑ i : ZMod n, (fixedVertices n (sr i)).card : ℕ) : ℝ) := by
        push_cast [permChar]; ring
    _ = (n : ℝ) := by rw [key, ZMod.card]

/-- **Main result.** For every regular `n`-gon (`n ≥ 1`), the permutation character of the
action of `DihedralGroup n` on the vertices contains the trivial character with multiplicity
`1`, the sign character with multiplicity `0`, and every two-dimensional rotation character
with multiplicity `1`. Taking `n = 5` recovers the pentagon case.

(For the parameters `j` for which `rotChar n j` is the character of a reducible
two-dimensional representation, such as `j = 0`, the stated number is the inner product
`⟨permChar, rotChar n j⟩`, which is still `1`.) -/
