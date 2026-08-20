import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma prime_not_dvd_factorial_of_lt {p i : ℕ} (hp : p.Prime) (hpi : i < p) :
    ¬ p ∣ i.factorial := by
  rw [hp.dvd_factorial]
  exact not_le_of_gt hpi

