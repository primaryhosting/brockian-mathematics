import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_eleven :
    ∃ m₀ : ℕ, 11 < m₀ ∧
      (m₀ + 11 - 1) ^ (11 + 1).primesBelow.card < Nat.choose (m₀ + 11 - 1) 11 ∧
      ∀ m : ℕ, 11 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 11) ∧ p.Prime ∧ 11 < p ∧ p ∣ j := by
  refine ⟨18, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_eleven hm

