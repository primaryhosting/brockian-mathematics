import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_twelve :
    ∃ m₀ : ℕ, 12 < m₀ ∧
      (m₀ + 12 - 1) ^ (12 + 1).primesBelow.card < Nat.choose (m₀ + 12 - 1) 12 ∧
      ∀ m : ℕ, 12 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 12) ∧ p.Prime ∧ 12 < p ∧ p ∣ j := by
  refine ⟨16, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_twelve hm

