import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_le_twenty {k : ℕ} (hk : 0 < k) (hk20 : k ≤ 20) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk16 : k ≤ 16
  · exact sylvester_schur_interval_threshold_le_sixteen hk hk16
  · interval_cases k
    · exact sylvester_schur_interval_threshold_seventeen
    · exact sylvester_schur_interval_threshold_eighteen
    · exact sylvester_schur_interval_threshold_nineteen
    · exact sylvester_schur_interval_threshold_twenty

