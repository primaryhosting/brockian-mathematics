import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_fourteen :
    ∃ m₀ : ℕ, 14 < m₀ ∧
      (m₀ + 14 - 1) ^ (14 + 1).primesBelow.card < Nat.choose (m₀ + 14 - 1) 14 ∧
      ∀ m : ℕ, 14 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 14) ∧ p.Prime ∧ 14 < p ∧ p ∣ j := by
  refine ⟨22, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_fourteen hm

