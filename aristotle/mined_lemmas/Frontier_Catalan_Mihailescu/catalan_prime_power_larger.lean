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

lemma catalan_prime_power_larger {x y p q r k : ℕ} (hr : r.Prime) (hxk : x = r ^ k) (hx : 1 < x)
    (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) (hqodd : Odd q) (h : x ^ p = y ^ q + 1) :
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  subst hxk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h'
    · simp at hx
    · exact h'
  have hm : 1 < k * p := by nlinarith
  have h' : r ^ (k * p) = y ^ q + 1 := by rw [pow_mul]; exact h
  obtain ⟨h1, h2, h3, h4⟩ := catalan_prime_pow_larger hr hy hq hqodd hm h'
  subst h1
  have hk : k = 1 ∧ p = 2 := by
    have hk2 : k ≤ 2 := Nat.le_of_dvd (by omega) ⟨p, h2.symm⟩
    interval_cases k <;> omega
  obtain ⟨hk1', hp2⟩ := hk
  subst hk1'
  exact ⟨by norm_num, hp2, h3, h4⟩

/-- If the larger base is a power of two there is no solution at all. -/
