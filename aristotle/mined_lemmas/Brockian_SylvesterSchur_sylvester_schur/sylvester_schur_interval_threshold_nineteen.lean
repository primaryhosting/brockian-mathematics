import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_nineteen :
    ∃ m₀ : ℕ, 19 < m₀ ∧
      (m₀ + 19 - 1) ^ (19 + 1).primesBelow.card < Nat.choose (m₀ + 19 - 1) 19 ∧
      ∀ m : ℕ, 19 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 19) ∧ p.Prime ∧ 19 < p ∧ p ∣ j := by
  refine ⟨33, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_nineteen hm

