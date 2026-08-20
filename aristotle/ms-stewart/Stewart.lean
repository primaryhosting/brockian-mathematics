import Mathlib
namespace Brockian.MsStewart
/-- Stewart's theorem: for a point D on segment BC of a triangle,
    |AB|²·|DC| + |AC|²·|BD| = |BC|·(|AD|² + |BD|·|DC|). -/
theorem stewart (A B C D : EuclideanSpace ℝ (Fin 2)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hD : D = B + t • (C - B)) :
    dist A B ^ 2 * dist D C + dist A C ^ 2 * dist B D
      = dist B C * (dist A D ^ 2 + dist B D * dist D C) := by
  sorry
end Brockian.MsStewart
