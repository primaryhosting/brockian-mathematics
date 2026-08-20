import Mathlib
namespace Brockian.Wolstenholme
/-- Wolstenholme's theorem: for a prime p ≥ 5, p^3 divides C(2p, p) − 2. -/
theorem wolstenholme (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ (Nat.choose (2 * p) p : ℤ) - 2 := by
  sorry
end Brockian.Wolstenholme
