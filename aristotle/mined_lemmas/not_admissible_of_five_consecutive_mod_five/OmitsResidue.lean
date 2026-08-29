import Mathlib


def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

