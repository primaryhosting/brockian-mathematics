import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_eight :
    ∃ m₀ : ℕ, 8 < m₀ ∧
      (m₀ + 8 - 1) ^ (8 + 1).primesBelow.card < Nat.choose (m₀ + 8 - 1) 8 ∧
      ∀ m : ℕ, 8 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 8) ∧ p.Prime ∧ 8 < p ∧ p ∣ j := by
  refine ⟨14, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_eight hm

