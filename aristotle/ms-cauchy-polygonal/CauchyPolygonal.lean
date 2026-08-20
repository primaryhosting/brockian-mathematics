import Mathlib
namespace Brockian.MsCauchyPolygonal
/-- Cauchy's polygonal number theorem: every natural number is a sum of s polygonal numbers of
    order s (s ≥ 3), where the k-th s-gonal number is (s-2)·k·(k-1)/2 + k. -/
theorem cauchy_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ f : Fin s → ℕ, n = ∑ i, ((s - 2) * (f i) * ((f i) - 1) / 2 + f i) := by
  sorry
end Brockian.MsCauchyPolygonal
