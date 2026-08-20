import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_fifteen :
    ∃ m₀ : ℕ, 15 < m₀ ∧
      (m₀ + 15 - 1) ^ (15 + 1).primesBelow.card < Nat.choose (m₀ + 15 - 1) 15 ∧
      ∀ m : ℕ, 15 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 15) ∧ p.Prime ∧ 15 < p ∧ p ∣ j := by
  refine ⟨20, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_fifteen hm

