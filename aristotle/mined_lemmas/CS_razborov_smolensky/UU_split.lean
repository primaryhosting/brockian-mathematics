import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem UU_split {ζ : F} (hζ : ζ ≠ 0) (S : Finset (Fin n)) :
    UU ζ Finset.univ * (∏ i ∈ Sᶜ, vv ζ i) = UU ζ S := by
  classical
  have h1 : UU ζ Finset.univ = UU ζ S * ∏ i ∈ Sᶜ, uu ζ i := by
    rw [UU, UU, ← Finset.prod_union (disjoint_compl_right)]
    congr 1
    simp
  rw [h1, mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun i _ => uu_mul_vv hζ i), Finset.prod_const_one, mul_one]

/-- The indicator function of a point of the cube. -/
