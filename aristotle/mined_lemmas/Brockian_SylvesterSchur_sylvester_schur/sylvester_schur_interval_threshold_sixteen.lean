import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_sixteen :
    ∃ m₀ : ℕ, 16 < m₀ ∧
      (m₀ + 16 - 1) ^ (16 + 1).primesBelow.card < Nat.choose (m₀ + 16 - 1) 16 ∧
      ∀ m : ℕ, 16 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 16) ∧ p.Prime ∧ 16 < p ∧ p ∣ j := by
  refine ⟨19, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_sixteen hm

