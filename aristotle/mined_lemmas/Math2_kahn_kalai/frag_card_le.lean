import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma frag_card_le {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    (frag H W S).card ≤ S.card :=
  Finset.card_le_card (frag_subset hS)

/-- Capture property: `W ∪ T(S,W)` contains an edge of `H`. -/
