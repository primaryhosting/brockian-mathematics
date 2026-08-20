import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_seven :
    ∃ m₀ : ℕ, 7 < m₀ ∧
      (m₀ + 7 - 1) ^ (7 + 1).primesBelow.card < Nat.choose (m₀ + 7 - 1) 7 ∧
      ∀ m : ℕ, 7 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 7) ∧ p.Prime ∧ 7 < p ∧ p ∣ j := by
  refine ⟨18, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_seven hm

