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

lemma catalan_prime_power_base {x y p q r k : ℕ} (hr : r.Prime) (hyk : y = r ^ k)
    (hx : 1 < x) (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) (h : x ^ p = y ^ q + 1) :
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  subst hyk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h'
    · simp at hy
    · exact h'
  have h' : x ^ p = r ^ (k * q) + 1 := by rw [pow_mul]; exact h
  have hn : 1 < k * q := by nlinarith
  obtain ⟨h1, h2, h3, h4⟩ := catalan_prime_base hr hx hp hn h'
  subst h3
  have hk3 : k ≤ 3 := Nat.le_of_dvd (by omega) ⟨q, h4.symm⟩
  have hkq : k = 1 ∧ q = 3 := by
    interval_cases k <;> omega
  obtain ⟨hk, hq3⟩ := hkq
  subst hk
  exact ⟨h1, h2, by norm_num, hq3⟩

/-! ### The larger base a prime power -/

/-- The auxiliary equation `z ^ r + 1 = r * (z + 1)` only has the solution `2 ^ 3 + 1 = 3 * 3`. -/
