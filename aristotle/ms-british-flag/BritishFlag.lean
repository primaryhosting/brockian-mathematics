import Mathlib
namespace Brockian.MsBritishFlag
/-- The British flag theorem: for a point P and a rectangle with corners A, A+u, A+u+v, A+v
    where u ⟂ v, dist(P,A)² + dist(P, A+u+v)² = dist(P, A+u)² + dist(P, A+v)². -/
theorem british_flag {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P A u v : E) (h : inner u v = (0 : ℝ)) :
    dist P A ^ 2 + dist P (A + u + v) ^ 2 = dist P (A + u) ^ 2 + dist P (A + v) ^ 2 := by
  sorry
end Brockian.MsBritishFlag
