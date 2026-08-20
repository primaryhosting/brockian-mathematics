import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_le_twenty {m k : ℕ} (hk : 0 < k) (hk20 : k ≤ 20)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk16 : k ≤ 16
  · exact sylvester_schur_interval_le_sixteen hk hk16 hm
  · interval_cases k
    · exact sylvester_schur_interval_seventeen (m := m) (by omega)
    · exact sylvester_schur_interval_eighteen (m := m) (by omega)
    · exact sylvester_schur_interval_nineteen (m := m) (by omega)
    · exact sylvester_schur_interval_twenty (m := m) (by omega)

