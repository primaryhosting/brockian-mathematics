import Mathlib
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/
theorem sylvester_schur (n k : ℕ) (h : k < n) (hk : 0 < k) :
    ∃ i ∈ Finset.range k, ∃ p, p.Prime ∧ k < p ∧ p ∣ (n + 1 + i) := by
  sorry
end Brockian.SylvesterSchur
