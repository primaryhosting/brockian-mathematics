import Mathlib
namespace Brockian.MsHermiteHadamard
/-- The Hermite–Hadamard inequality: for a convex f on [a,b] with a < b,
    f((a+b)/2) ≤ (1/(b−a)) ∫_a^b f ≤ (f a + f b)/2. -/
theorem hermite_hadamard (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  sorry
end Brockian.MsHermiteHadamard
