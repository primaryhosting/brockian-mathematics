import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem supported_ext {n : ℕ} (a : ℕ) (x : Cube n) :
    Supported (n + a) (ext (fun i => decide (i < n + a)) x) := by
  intro i hi
  have : ¬ (i < n) := by omega
  simp [ext, this]
  omega

