import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem size_le_of_mem {cs : List Circuit} {c : Circuit} (h : c ∈ cs) :
    c.size ≤ (cs.map size).sum :=
  List.single_le_sum (by simp) _ (List.mem_map_of_mem h)

