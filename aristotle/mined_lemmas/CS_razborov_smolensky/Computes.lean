import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def Computes (q n : ℕ) (C : Circuit) (f : (ℕ → Bool) → Bool) : Prop :=
  ∀ x, Supported n x → C.eval q x = f x

/-- `f ∈ AC⁰[q]`: there is a family of circuits with `MOD q` gates of constant depth and
polynomial size computing `f`. -/
