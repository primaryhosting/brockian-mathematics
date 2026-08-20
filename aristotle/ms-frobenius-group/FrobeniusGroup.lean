import Mathlib
namespace Brockian.MsFrobeniusGroup
/-- Frobenius's theorem: for a finite group G and any n, gcd(n, |G|) divides the number of
    solutions of xⁿ = 1 in G. -/
theorem frobenius_group (G : Type*) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) :
    Nat.gcd n (Fintype.card G) ∣ (Finset.univ.filter (fun g : G => g ^ n = 1)).card := by
  sorry
end Brockian.MsFrobeniusGroup
