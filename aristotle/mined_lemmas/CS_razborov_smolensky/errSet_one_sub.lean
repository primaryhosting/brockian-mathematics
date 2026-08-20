import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem errSet_one_sub {n : ℕ} (P : Cube n → F) (v : Cube n → Bool) :
    errSet (1 - P) (fun x => !(v x)) = errSet P v := by
  ext x
  simp only [mem_errSet, Pi.sub_apply, Pi.one_apply, bitv_not]
  constructor
  · intro h hc; exact h (by rw [hc])
  · intro h hc; exact h (sub_right_injective hc)

omit hq [CharP F q] in
/-- The data extracted from the inductive hypothesis at a gate with children `cs`. -/
