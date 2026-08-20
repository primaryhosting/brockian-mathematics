import Mathlib
namespace Brockian.MsErdosAnning
/-- The Erdős–Anning theorem: an infinite set of points in the plane with all pairwise distances
    integers must be collinear. -/
theorem erdos_anning (S : Set (EuclideanSpace ℝ (Fin 2))) (hinf : S.Infinite)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n) :
    ∃ (p v : EuclideanSpace ℝ (Fin 2)), ∀ x ∈ S, ∃ t : ℝ, x = p + t • v := by
  sorry
end Brockian.MsErdosAnning
