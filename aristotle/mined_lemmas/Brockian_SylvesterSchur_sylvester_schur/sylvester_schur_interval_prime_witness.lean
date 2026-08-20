import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_prime_witness {m k p : ℕ}
    (hlo : m ≤ p) (hhi : p < m + k) (hp : p.Prime) (hkp : k < p) :
    ∃ j q : ℕ, j ∈ Set.Ico m (m + k) ∧ q.Prime ∧ k < q ∧ q ∣ j :=
  ⟨p, p, ⟨hlo, hhi⟩, hp, hkp, dvd_rfl⟩

