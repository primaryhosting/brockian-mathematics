import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem mon_eq_ite {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    (mon S : Cube n → F) x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  unfold mon
  split
  · rename_i h
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rename_i h
    push_neg at h
    obtain ⟨i, hi, hx⟩ := h
    refine Finset.prod_eq_zero hi ?_
    have hxf : x i = false := by simpa using hx
    simp [hxf]

