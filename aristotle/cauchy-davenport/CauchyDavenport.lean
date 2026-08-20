import Mathlib
namespace Brockian.CauchyDavenport
/-- The Cauchy–Davenport theorem: for a prime p and nonempty A,B ⊆ ℤ/p,
    |A+B| ≥ min(p, |A|+|B|−1). -/
theorem cauchy_davenport {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by
  sorry
end Brockian.CauchyDavenport
