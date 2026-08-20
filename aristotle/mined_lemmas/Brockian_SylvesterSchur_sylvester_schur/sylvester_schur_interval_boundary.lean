import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_boundary {k : ℕ} (hk : 0 < k) :
    ∃ j p : ℕ, j ∈ Set.Ico (k + 1) (k + 1 + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  obtain ⟨p, hp, hkp, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul k hk.ne'
  refine ⟨p, p, ?_, hp, hkp, dvd_rfl⟩
  exact ⟨Nat.succ_le_of_lt hkp, by omega⟩

