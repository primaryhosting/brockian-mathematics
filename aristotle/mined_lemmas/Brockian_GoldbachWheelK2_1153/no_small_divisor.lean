/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`n` is at least `2` and its only divisors are `1` and `n`. -/

theorem no_small_divisor {n : Nat} (h : wheelPrime n = true) {q : Nat}
    (hq2 : 2 ≤ q) (hq36 : q ≤ 36) (hqn : q < n) (hqd : q ∣ n) : False := by
  rw [wheelPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  obtain ⟨p, hp, hpq⟩ := exists_spoke_dvd q (List.mem_range.2 (by omega)) hq2
  have hpn : p ∣ n := Nat.dvd_trans hpq hqd
  have hspoke := hall p hp
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hspoke
  have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hpn
  have hnp : n = p := by
    rcases hspoke with h1 | h1
    · exact h1
    · exact absurd hmod h1
  have hpq' : p ≤ q := Nat.le_of_dvd (by omega) hpq
  have hqn' : q ≤ n := Nat.le_of_dvd (by omega) hqd
  omega

/-- Correctness of the wheel test in its range of validity. -/
