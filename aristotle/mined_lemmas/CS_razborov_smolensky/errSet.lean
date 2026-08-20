import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


noncomputable def errSet {n : ℕ} (P : Cube n → F) (v : Cube n → Bool) : Finset (Cube n) :=
  Finset.univ.filter (fun x => P x ≠ bitv F (v x))

open Classical in
