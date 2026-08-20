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

lemma sum_dihedral [NeZero n] (f : DihedralGroup n → ℝ) :
    ∑ g : DihedralGroup n, f g = (∑ i : ZMod n, f (r i)) + ∑ i : ZMod n, f (sr i) := by
  classical
  let e : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n :=
    { toFun := Sum.elim DihedralGroup.r DihedralGroup.sr
      invFun := fun g => match g with
        | DihedralGroup.r i => Sum.inl i
        | DihedralGroup.sr i => Sum.inr i
      left_inv := by rintro (x | x) <;> rfl
      right_inv := by rintro (x | x) <;> rfl }
  rw [← Equiv.sum_comp e f, Fintype.sum_sum_type]
  rfl

