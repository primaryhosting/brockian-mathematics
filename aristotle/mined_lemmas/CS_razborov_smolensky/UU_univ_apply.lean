import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem UU_univ_apply {n : ℕ} (ζ : F) (x : Cube n) : UU ζ univ x = ζ ^ (wt x) := by
  classical
  have h : ∀ i : Fin n, uu ζ i x = ζ ^ (if x i = true then 1 else 0) := by
    intro i
    cases h : x i <;> simp [uu, h]
  rw [UU, Finset.prod_apply, Finset.prod_congr rfl (fun i _ => h i),
    Finset.prod_pow_eq_pow_sum]
  congr 1
  simp [wt, Finset.sum_boole]

/-! ### Roots of unity -/

