import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem mon_mem_Deg {n d : ℕ} {S : Finset (Fin n)} (h : S.card ≤ d) :
    (mon S : Cube n → F) ∈ Deg F n d :=
  Submodule.subset_span ⟨S, h, rfl⟩

