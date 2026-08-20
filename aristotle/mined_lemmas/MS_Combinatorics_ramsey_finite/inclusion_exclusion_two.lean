import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

theorem inclusion_exclusion_two {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  have := Finset.card_union_add_card_inter A B
  omega

