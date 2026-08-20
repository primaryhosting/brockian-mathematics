import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem UU_mem_Deg (ζ : F) (S : Finset (Fin n)) : UU ζ S ∈ Deg F n S.card := by
  have := prod_mem_Deg (F := F) S (fun i => uu ζ i) 1 (fun i _ => uu_mem_Deg ζ i)
  simpa [UU] using this

