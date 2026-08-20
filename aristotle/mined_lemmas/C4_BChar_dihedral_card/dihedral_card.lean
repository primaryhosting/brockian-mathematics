import Mathlib
namespace C4.BChar

/-- The dihedral group of order `2n` has exactly `2n` elements. -/

theorem dihedral_card (n : ℕ) [NeZero n] : Nat.card (DihedralGroup n) = 2*n :=
  DihedralGroup.nat_card

/-- The unit group of `ZMod 5` has 4 elements. -/
