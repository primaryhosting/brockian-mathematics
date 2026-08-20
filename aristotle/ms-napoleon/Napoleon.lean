import Mathlib
namespace Brockian.MsNapoleon
/-- Napoleon's theorem (complex form): the centroids of the outward equilateral triangles
    erected on the sides of any triangle a,b,c ∈ ℂ themselves form an equilateral triangle.
    With ω = primitive cube root of unity, the three outer apexes n₁,n₂,n₃ satisfy
    n₁ + ω·n₂ + ω²·n₃ = 0 for the centroids. -/
theorem napoleon (a b c : ℂ) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    let g₁ := (b + c + (c - b) * (-ω)) / 3
    let g₂ := (c + a + (a - c) * (-ω)) / 3
    let g₃ := (a + b + (b - a) * (-ω)) / 3
    g₁ + ω * g₂ + ω ^ 2 * g₃ = 0 := by
  sorry
end Brockian.MsNapoleon
