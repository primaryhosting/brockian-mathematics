import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_thirteen :
    ∃ m₀ : ℕ, 13 < m₀ ∧
      (m₀ + 13 - 1) ^ (13 + 1).primesBelow.card < Nat.choose (m₀ + 13 - 1) 13 ∧
      ∀ m : ℕ, 13 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 13) ∧ p.Prime ∧ 13 < p ∧ p ∣ j := by
  refine ⟨24, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_thirteen hm

