import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_nine :
    ∃ m₀ : ℕ, 9 < m₀ ∧
      (m₀ + 9 - 1) ^ (9 + 1).primesBelow.card < Nat.choose (m₀ + 9 - 1) 9 ∧
      ∀ m : ℕ, 9 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 9) ∧ p.Prime ∧ 9 < p ∧ p ∣ j := by
  refine ⟨12, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_nine hm

