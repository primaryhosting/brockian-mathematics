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

theorem isPrime_of_wheelPrime {n : Nat} (hn : n < 1369) (h : wheelPrime n = true) :
    IsPrime n := by
  have h2 : 2 ≤ n := by
    rw [wheelPrime, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  refine ⟨h2, ?_⟩
  intro d hd
  apply Classical.byContradiction
  intro hcon
  have hd1 : d ≠ 1 := fun h => hcon (Or.inl h)
  have hdn : d ≠ n := fun h => hcon (Or.inr h)
  obtain ⟨e, he⟩ := hd
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mul] at he
    omega
  have hd2 : 2 ≤ d := by omega
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) ⟨e, he⟩
  have hdlt : d < n := by omega
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · have hcase : e = 0 ∨ e = 1 := by omega
      rcases hcase with rfl | rfl <;> omega
    · exact hge
  have helt : e < n := by
    have hc : e * d = d * e := Nat.mul_comm e d
    have : e * 2 ≤ e * d := Nat.mul_le_mul_left e hd2
    omega
  rcases Nat.le_total d e with hde | hde
  · have hsq : d * d ≤ n := by
      have : d * d ≤ d * e := Nat.mul_le_mul_left d hde
      omega
    have hd36 : d ≤ 36 := by
      apply Classical.byContradiction
      intro hc
      have : 37 * 37 ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact no_small_divisor h hd2 hd36 hdlt ⟨e, he⟩
  · have hsq : e * e ≤ n := by
      have : e * e ≤ d * e := Nat.mul_le_mul_right e hde
      omega
    have he36 : e ≤ 36 := by
      apply Classical.byContradiction
      intro hc
      have : 37 * 37 ≤ e * e := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact no_small_divisor h he2 he36 helt ⟨d, by rw [he]; exact Nat.mul_comm d e⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The finite Goldbach computation: for every `m` with `2 ≤ m ≤ 576` — that is, for
every even number `2 * m` between `4` and `1152` — there is a prime `p < 100` such that
both `p` and `2 * m - p` pass the wheel test. -/
