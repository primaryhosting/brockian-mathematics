import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

theorem capset_card_le {n : ℕ} (A : Finset (Fin n → ZMod 3))
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) :
    A.card ≤ 3 * (lowExp n).card := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have key := card_le_of_diag_decomp (F := ZMod 3) (X := A)
    (I₁ := (lowExp n : Finset (Exp n))) (I₂ := (lowExp n : Finset (Exp n)))
    (I₃ := (lowExp n : Finset (Exp n)))
    (f₁ := fun a x => mon n (a : Exp n) (x : Fin n → ZMod 3))
    (g₁ := fun a y z => S₁ n (a : Exp n) (y : Fin n → ZMod 3) (z : Fin n → ZMod 3))
    (f₂ := fun a y => mon n (a : Exp n) (y : Fin n → ZMod 3))
    (g₂ := fun a x z => S₂ n (a : Exp n) (x : Fin n → ZMod 3) (z : Fin n → ZMod 3))
    (f₃ := fun a z => mon n (a : Exp n) (z : Fin n → ZMod 3))
    (g₃ := fun a x y => S₃ n (a : Exp n) (x : Fin n → ZMod 3) (y : Fin n → ZMod 3))
    (by
      intro x y z
      rw [indicator_diag hA x y z, indicator_slices]
      congr 1
      · congr 1
        · exact (Finset.sum_coe_sort (lowExp n)
            (fun a => mon n a (x : Fin n → ZMod 3) * S₁ n a y z)).symm
        · exact (Finset.sum_coe_sort (lowExp n)
            (fun a => mon n a (y : Fin n → ZMod 3) * S₂ n a x z)).symm
      · exact (Finset.sum_coe_sort (lowExp n)
          (fun a => mon n a (z : Fin n → ZMod 3) * S₃ n a x y)).symm)
  simp only [Fintype.card_coe] at key
  omega

end CapSetAux

import RequestProject.SliceRank

/-!
# The Croot–Lev–Pach polynomial expansion for `𝔽₃ⁿ`

We expand the indicator function of `x + y + z = 0` on `(ZMod 3)ⁿ` into monomials and
group the resulting terms into three families of slices, each indexed by the set of
exponent vectors of degree at most `2n/3`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- Coefficients of the expansion of `1 - (u+v+w)^2` over `ZMod 3`. -/
