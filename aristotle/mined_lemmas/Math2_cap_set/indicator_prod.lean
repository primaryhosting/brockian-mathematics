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

lemma indicator_prod (x y z : Fin n → ZMod 3) :
    (if x + y + z = 0 then (1 : ZMod 3) else 0)
      = ∏ i, (if x i + y i + z i = 0 then (1 : ZMod 3) else 0) := by
  by_cases h : x + y + z = 0
  · rw [if_pos h]
    refine (Finset.prod_eq_one fun i _ => ?_).symm
    have : x i + y i + z i = 0 := by
      have := congrFun h i
      simpa using this
    rw [if_pos this]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    have : x i + y i + z i ≠ 0 := by simpa using hi
    rw [if_neg this]

/-- The main expansion: the indicator of `x + y + z = 0` as a sum of products of monomials. -/
