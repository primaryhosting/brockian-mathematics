import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_five :
    ∃ m₀ : ℕ, 5 < m₀ ∧
      (m₀ + 5 - 1) ^ (5 + 1).primesBelow.card < Nat.choose (m₀ + 5 - 1) 5 ∧
      ∀ m : ℕ, 5 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 5) ∧ p.Prime ∧ 5 < p ∧ p ∣ j := by
  refine ⟨12, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_five hm

