import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


@[simp] theorem depth_cand (cs) :
    (Circuit.cand cs).depth = (cs.map depth).foldr max 0 + 1 := by simp [depth]
