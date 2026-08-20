import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

private def MonoColor {V : Type} (f : Sym2 V → Bool) (c : Bool) (A : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → f s(x, y) = c

/-- Finite Ramsey theorem, in the form needed for the induction: for all `r s` there is an
`N` such that any `2`-colouring of the edges on any set `S` with `N ≤ S.card` contains a
red set of size `r` or a blue set of size `s` inside `S`. -/
