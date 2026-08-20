import Mathlib
namespace Brockian.WolstenholmeHarmonic
/-- Wolstenholme's harmonic form: for a prime p ≥ 5, p² divides the numerator of the
    harmonic sum H_{p-1} = ∑_{k=1}^{p-1} 1/k. -/
theorem wolstenholme_harmonic (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ (∑ k ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (k : ℚ)).num := by
  sorry
end Brockian.WolstenholmeHarmonic
