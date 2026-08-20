import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_le_eleven {m k : ℕ} (hk : 0 < k) (hk11 : k ≤ 11)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)
  · exact sylvester_schur_interval_seven (m := m) (by omega)
  · exact sylvester_schur_interval_eight (m := m) (by omega)
  · exact sylvester_schur_interval_nine (m := m) (by omega)
  · exact sylvester_schur_interval_ten (m := m) (by omega)
  · exact sylvester_schur_interval_eleven (m := m) (by omega)

