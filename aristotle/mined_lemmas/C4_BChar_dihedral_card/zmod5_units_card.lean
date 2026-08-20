import Mathlib
namespace C4.BChar

/-- The dihedral group of order `2n` has exactly `2n` elements. -/

theorem zmod5_units_card : Fintype.card (ZMod 5)ˣ = 4 := by decide

/-- `(ZMod 5)ˣ` is cyclic of order 4: `2` is a generator. -/
