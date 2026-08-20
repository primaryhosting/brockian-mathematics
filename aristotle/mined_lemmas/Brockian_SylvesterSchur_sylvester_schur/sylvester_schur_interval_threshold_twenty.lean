import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_twenty :
    ∃ m₀ : ℕ, 20 < m₀ ∧
      (m₀ + 20 - 1) ^ (20 + 1).primesBelow.card < Nat.choose (m₀ + 20 - 1) 20 ∧
      ∀ m : ℕ, 20 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 20) ∧ p.Prime ∧ 20 < p ∧ p ∣ j := by
  refine ⟨31, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_twenty hm

