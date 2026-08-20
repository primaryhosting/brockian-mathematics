import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_ten :
    ∃ m₀ : ℕ, 10 < m₀ ∧
      (m₀ + 10 - 1) ^ (10 + 1).primesBelow.card < Nat.choose (m₀ + 10 - 1) 10 ∧
      ∀ m : ℕ, 10 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 10) ∧ p.Prime ∧ 10 < p ∧ p ∣ j := by
  refine ⟨11, by omega, by decide, ?_⟩
  intro m hm hlt
  omega

