import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_le_four {k : ℕ} (hk : 0 < k) (hk4 : k ≤ 4) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · refine ⟨2, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm
  · refine ⟨3, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm
  · refine ⟨7, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm
  · refine ⟨5, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm

