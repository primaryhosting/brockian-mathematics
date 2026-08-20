/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


theorem oddPerfect_euler_form {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  have hnpos : 0 < n := hperf.2
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hsigma : (sigma 1) n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hnpos).mp hperf
  obtain ⟨p, hp_mem, hp_geom, hother⟩ := exceptional_prime_data hn hodd hsigma
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hpodd : p % 2 = 1 := by
    rw [← Nat.odd_iff]
    exact hodd.of_dvd_nat (Nat.mem_primeFactors.mp hp_mem).2.1
  obtain ⟨hp4, hk4⟩ := geom_sum_mod_four hpodd hp_geom
  obtain ⟨m, hpm, hform⟩ :=
    reconstruct_euler_factorization hn hp rfl hother
  exact ⟨p, n.factorization p, m, hp, hp4, hk4, hpm, hform⟩

end Brockian.OddPerfectEuler

