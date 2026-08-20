import Mathlib
namespace Brockian.MsSchurInequality

/-- Schur's inequality in the sorted case `0 ≤ z ≤ y ≤ x`. -/

theorem schur_inequality (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    0 ≤ x ^ t * (x - y) * (x - z) + y ^ t * (y - x) * (y - z) + z ^ t * (z - x) * (z - y) := by
  rcases le_total x y with h1 | h1 <;> rcases le_total y z with h2 | h2 <;>
    rcases le_total x z with h3 | h3
  · have h := schur_sorted z y x t hx h1 h2 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted z y x t hx h1 h2 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted y z x t hx h3 h2 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted y x z t hz h3 h1 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted z x y t hy h1 h3 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted x z y t hy h2 h3 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted x y z t hz h2 h1 ht; ring_nf at h ⊢; linarith
  · have h := schur_sorted x y z t hz h2 h1 ht; ring_nf at h ⊢; linarith

end Brockian.MsSchurInequality

