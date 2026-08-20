import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem eval_cand (q cs x) : eval q (.cand cs) x = (cs.map (fun c => c.eval q x)).all id := by
  simp [eval]
