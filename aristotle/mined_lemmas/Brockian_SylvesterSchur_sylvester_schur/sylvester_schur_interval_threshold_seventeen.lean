import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_seventeen :
    ∃ m₀ : ℕ, 17 < m₀ ∧
      (m₀ + 17 - 1) ^ (17 + 1).primesBelow.card < Nat.choose (m₀ + 17 - 1) 17 ∧
      ∀ m : ℕ, 17 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 17) ∧ p.Prime ∧ 17 < p ∧ p ∣ j := by
  refine ⟨26, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_seventeen hm

