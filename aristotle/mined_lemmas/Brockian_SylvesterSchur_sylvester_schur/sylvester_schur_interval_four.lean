import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_four {m : ℕ} (hm : 4 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 4) ∧ p.Prime ∧ 4 < p ∧ p ∣ j := by
  obtain ⟨j, p, hj, hp, hpgt3, hpj⟩ := sylvester_schur_interval_three (m := m) (by omega)
  have hp_ne4 : p ≠ 4 := by
    intro hp4
    subst hp4
    norm_num at hp
  have hpgt4 : 4 < p := by omega
  have hjhi : j < m + 4 := by
    have : j < m + 3 := hj.2
    omega
  exact ⟨j, p, ⟨hj.1, hjhi⟩, hp, hpgt4, hpj⟩

