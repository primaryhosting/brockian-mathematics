import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_le_four {m k : ℕ} (hk : 0 < k) (hk4 : k ≤ 4) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)

