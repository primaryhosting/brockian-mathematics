import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


@[simp] theorem mem_errSet {n : ℕ} {P : Cube n → F} {v : Cube n → Bool} {x : Cube n} :
    x ∈ errSet P v ↔ P x ≠ bitv F (v x) := by simp [errSet]

open Classical in
