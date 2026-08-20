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

noncomputable def twoDimRep (n : ℕ) [NeZero n] (j : ℕ) :
    DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := match g with
    | DihedralGroup.r i => !![rootPow n j i, 0; 0, rootPow n j (-i)]
    | DihedralGroup.sr i => !![0, rootPow n j (-i); rootPow n j i, 0]
  map_one' := by
    show !![rootPow n j 0, 0; 0, rootPow n j (-0)] = 1
    rw [Matrix.one_fin_two, neg_zero, rootPow_zero]
  map_mul' g h := by
    cases g with
    | r a =>
      cases h with
      | r b =>
        show !![rootPow n j (a + b), 0; 0, rootPow n j (-(a + b))] = _ * _
        rw [Matrix.mul_fin_two, rootPow_add, show -(a + b) = (-a) + (-b) by ring, rootPow_add]
        norm_num
      | sr b =>
        show !![0, rootPow n j (-(b - a)); rootPow n j (b - a), 0] = _ * _
        rw [Matrix.mul_fin_two, show b - a = b + (-a) by ring, rootPow_add,
          show -(b + -a) = (-b) + a by ring, rootPow_add]
        norm_num
        constructor <;> ring
    | sr a =>
      cases h with
      | r b =>
        show !![0, rootPow n j (-(a + b)); rootPow n j (a + b), 0] = _ * _
        rw [Matrix.mul_fin_two, rootPow_add, show -(a + b) = (-a) + (-b) by ring, rootPow_add]
        norm_num
      | sr b =>
        show !![rootPow n j (b - a), 0; 0, rootPow n j (-(b - a))] = _ * _
        rw [Matrix.mul_fin_two, show b - a = b + (-a) by ring, rootPow_add,
          show -(b + -a) = (-b) + a by ring, rootPow_add]
        norm_num
        constructor <;> ring

/-- `rotChar n j` is the character (trace) of the two-dimensional representation
`twoDimRep n j`. -/
