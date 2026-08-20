import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_threshold_le_eight {k : ℕ} (hk : 0 < k) (hk8 : k ≤ 8) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_eight

