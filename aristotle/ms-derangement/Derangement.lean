import Mathlib
namespace Brockian.MsDerangement
/-- Closed form for derangements: Dₙ = n!·∑_{k=0}^{n} (−1)ᵏ/k!. -/
theorem derangement_closed (n : ℕ) :
    (Nat.numDerangements n : ℚ)
      = (n.factorial : ℚ) * ∑ k ∈ Finset.range (n + 1), (-1) ^ k / (k.factorial : ℚ) := by
  sorry
end Brockian.MsDerangement
