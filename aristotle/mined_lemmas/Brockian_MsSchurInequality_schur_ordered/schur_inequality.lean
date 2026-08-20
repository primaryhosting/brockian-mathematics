import Mathlib
namespace Brockian.MsSchurInequality

/-- Schur's inequality in the case of an ordered triple `z ≤ y ≤ x` with `0 ≤ z`. -/

theorem schur_inequality (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    0 ≤ x ^ t * (x - y) * (x - z) + y ^ t * (y - x) * (y - z) + z ^ t * (z - x) * (z - y) := by
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz
  · exact le_of_le_of_eq (schur_ordered z y x t hx hxy hyz ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered z y x t hx hxy hyz ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered y z x t hx hxz hyz ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered y x z t hz hxz hxy ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered z x y t hy hxy hxz ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered x z y t hy hyz hxz ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered x y z t hz hyz hxy ht) (by ring)
  · exact le_of_le_of_eq (schur_ordered x y z t hz hyz hxy ht) (by ring)

end Brockian.MsSchurInequality

