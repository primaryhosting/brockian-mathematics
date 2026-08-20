import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_six :
    ∃ m₀ : ℕ, 6 < m₀ ∧
      (m₀ + 6 - 1) ^ (6 + 1).primesBelow.card < Nat.choose (m₀ + 6 - 1) 6 ∧
      ∀ m : ℕ, 6 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 6) ∧ p.Prime ∧ 6 < p ∧ p ∣ j := by
  refine ⟨9, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_six hm

