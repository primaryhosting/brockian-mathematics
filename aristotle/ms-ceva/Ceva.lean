import Mathlib
namespace Brockian.MsCeva
/-- Ceva's theorem (ratio form): if D,E,F lie on segments BC,CA,AB with parameters splitting
    them in ratios giving points D=B+u(C−B), E=C+v(A−C), F=A+w(B−A), then the cevians AD,BE,CF
    are concurrent iff (u/(1−u))·(v/(1−v))·(w/(1−w)) = 1. -/
theorem ceva (A B C : EuclideanSpace ℝ (Fin 2)) (u v w : ℝ)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) (hw : 0 < w ∧ w < 1)
    (D E F : EuclideanSpace ℝ (Fin 2))
    (hD : D = B + u • (C - B)) (hE : E = C + v • (A - C)) (hF : F = A + w • (B - A)) :
    (∃ P : EuclideanSpace ℝ (Fin 2),
       (∃ s, P = A + s • (D - A)) ∧ (∃ t, P = B + t • (E - B)) ∧ (∃ r, P = C + r • (F - C)))
    ↔ (u / (1 - u)) * (v / (1 - v)) * (w / (1 - w)) = 1 := by
  sorry
end Brockian.MsCeva
