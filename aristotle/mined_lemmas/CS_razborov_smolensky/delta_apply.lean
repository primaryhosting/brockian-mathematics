import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem delta_apply (y x : Cube n) : (delta y : Cube n → F) x = if x = y then 1 else 0 := by
  unfold delta
  split
  · rename_i h
    subst h
    refine Finset.prod_eq_one fun i _ => ?_
    cases h : x i <;> simp
  · rename_i h
    have : ∃ i, x i ≠ y i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    obtain ⟨i, hi⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hy : y i <;> cases hx : x i <;> simp_all

/-- Each point indicator lies in the span of the products `∏_{i∈S} ζ^(x i)`. -/
