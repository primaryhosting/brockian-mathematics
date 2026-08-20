import Mathlib
namespace Brockian.MsMenelaus
/-- Menelaus's theorem: points D,E,F on lines BC,CA,AB (parameters u,v,w) are collinear iff the
    product of signed ratios (u/(1−u))·(v/(1−v))·(w/(1−w)) = −1. -/
theorem menelaus (A B C : EuclideanSpace ℝ (Fin 2)) (u v w : ℝ)
    (hu : u ≠ 1) (hv : v ≠ 1) (hw : w ≠ 1)
    (D E F : EuclideanSpace ℝ (Fin 2))
    (hD : D = B + u • (C - B)) (hE : E = C + v • (A - C)) (hF : F = A + w • (B - A)) :
    Collinear ℝ ({D, E, F} : Set (EuclideanSpace ℝ (Fin 2)))
      ↔ (u / (1 - u)) * (v / (1 - v)) * (w / (1 - w)) = -1 := by
  sorry
end Brockian.MsMenelaus
