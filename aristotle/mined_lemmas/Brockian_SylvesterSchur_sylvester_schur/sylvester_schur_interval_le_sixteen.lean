import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_le_sixteen {m k : ℕ} (hk : 0 < k) (hk16 : k ≤ 16)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk12 : k ≤ 12
  · exact sylvester_schur_interval_le_twelve hk hk12 hm
  · interval_cases k
    · exact sylvester_schur_interval_thirteen (m := m) (by omega)
    · exact sylvester_schur_interval_fourteen (m := m) (by omega)
    · exact sylvester_schur_interval_fifteen (m := m) (by omega)
    · exact sylvester_schur_interval_sixteen (m := m) (by omega)

