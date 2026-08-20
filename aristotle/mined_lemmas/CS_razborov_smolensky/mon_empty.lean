import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


@[simp] theorem mon_empty {n : ℕ} : (mon (∅ : Finset (Fin n)) : Cube n → F) = 1 := by
  funext x; simp [mon]

