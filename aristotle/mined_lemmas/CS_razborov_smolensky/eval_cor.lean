import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem eval_cor (q cs x) : eval q (.cor cs) x = (cs.map (fun c => c.eval q x)).any id := by
  simp [eval]
