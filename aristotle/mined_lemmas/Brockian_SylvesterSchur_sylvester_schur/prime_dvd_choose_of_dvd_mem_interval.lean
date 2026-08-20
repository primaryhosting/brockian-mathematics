import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma prime_dvd_choose_of_dvd_mem_interval
    {n i p j : ℕ} (hi_le_n : i ≤ n) (hp : p.Prime) (hip : i < p)
    (hj : j ∈ Set.Ico (n - i + 1) (n + 1)) (hpj : p ∣ j) :
    p ∣ Nat.choose n i := by
  have htop : n - i + 1 + i = n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun t => t + 1) (Nat.sub_add_cancel hi_le_n)
  have hj_dvd : j ∣ (n - i + 1).ascFactorial i := by
    have hhi : j < n - i + 1 + i := by simpa [htop] using hj.2
    exact dvd_ascFactorial_of_mem hj.1 hhi
  have hchoose :
      (n - i + 1).ascFactorial i = i.factorial * Nat.choose n i := by
    simpa [Nat.sub_add_cancel hi_le_n] using
      (Nat.ascFactorial_eq_factorial_mul_choose (n - i) i)
  have hp_dvd_mul : p ∣ i.factorial * Nat.choose n i := by
    exact hpj.trans (hchoose ▸ hj_dvd)
  exact (hp.dvd_mul.mp hp_dvd_mul).resolve_left
    (prime_not_dvd_factorial_of_lt hp hip)

