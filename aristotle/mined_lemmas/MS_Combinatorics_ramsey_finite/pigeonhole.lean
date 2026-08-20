import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

theorem pigeonhole {A B : Type*} [Fintype A] [Fintype B]
    (h : Fintype.card B < Fintype.card A) (f : A → B) : ¬ Function.Injective f := by
  intro hf
  exact absurd (Fintype.card_le_of_injective f hf) (by omega)

end MS.Combinatorics

