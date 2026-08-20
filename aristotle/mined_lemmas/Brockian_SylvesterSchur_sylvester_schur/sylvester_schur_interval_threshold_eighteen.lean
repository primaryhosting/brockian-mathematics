import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_eighteen :
    ∃ m₀ : ℕ, 18 < m₀ ∧
      (m₀ + 18 - 1) ^ (18 + 1).primesBelow.card < Nat.choose (m₀ + 18 - 1) 18 ∧
      ∀ m : ℕ, 18 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 18) ∧ p.Prime ∧ 18 < p ∧ p ∣ j := by
  refine ⟨24, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_eighteen hm

