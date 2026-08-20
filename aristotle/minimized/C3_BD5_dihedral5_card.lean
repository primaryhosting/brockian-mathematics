import Mathlib
namespace C3.BD5

/-- The dihedral group of order 10 (symmetries of the regular pentagon) has 10 elements. -/

theorem dihedral5_card : Nat.card (DihedralGroup 5) = 10 := by
  simp [Nat.card_eq_fintype_card, DihedralGroup.card]

/-- The golden ratio satisfies `φ² = φ + 1`. -/
