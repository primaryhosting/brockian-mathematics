import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_prime_pow_larger {y q r m : ℕ} (hr : r.Prime) (hy : 1 < y) (hq : 1 < q)
    (hqodd : Odd q) (hm : 1 < m) (h : r ^ m = y ^ q + 1) : r = 3 ∧ m = 2 ∧ y = 2 ∧ q = 3 := by
  rcases eq_or_ne r 2 with rfl | hr2
  · exact absurd h (catalan_two_pow_sub_one hy hm hq)
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨q', rfl⟩ := catalan_stage_one hr hr3 hy hq hqodd h
  have hq'1 : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with rfl | h'
    · simp at hq
    · exact h'
  have hz : 2 ≤ y ^ q' := by
    calc 2 ≤ y := hy
    _ = y ^ 1 := (pow_one y).symm
    _ ≤ y ^ q' := Nat.pow_le_pow_right (by omega) hq'1
  have hstage : r ^ m = (y ^ q') ^ r + 1 := by rw [← pow_mul, mul_comm q' r]; exact h
  obtain ⟨h1, h2, h3⟩ := catalan_stage_two hr hrodd hr3 hz hstage
  have hy2 : y = 2 ∧ q' = 1 := by
    rcases Nat.lt_or_ge q' 2 with hlt | hge
    · have hq'eq : q' = 1 := by omega
      subst hq'eq
      simpa using h2
    · exfalso
      have hpow : y ^ 2 ≤ y ^ q' := Nat.pow_le_pow_right (by omega) hge
      nlinarith [h2, hpow]
  obtain ⟨hy2', hq'2⟩ := hy2
  subst hq'2
  exact ⟨h1, h3, hy2', by omega⟩

/-- **Catalan's equation when the larger base is a prime power and `q` is odd.**
The only solution is `3 ^ 2 - 2 ^ 3 = 1`. -/
