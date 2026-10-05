import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

theorem catalan_coprime_exponents {x p y q : ℕ} (h : IsCatalanSolution x p y q) :
    Nat.Coprime p q := by
  obtain ⟨hx, hp, hy, hq, heq⟩ := h
  by_contra hc
  set d := Nat.gcd p q with hd
  have hdp : d ∣ p := Nat.gcd_dvd_left p q
  have hdq : d ∣ q := Nat.gcd_dvd_right p q
  have hd0 : d ≠ 0 := by
    intro h0
    have : p = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
    omega
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · have hd1 : d = 1 := by omega
      exact absurd (show Nat.Coprime p q by rw [Nat.Coprime, ← hd]; exact hd1) hc
    · exact h
  have hxp : x ^ p = (x ^ (p / d)) ^ d := by
    rw [← pow_mul, Nat.div_mul_cancel hdp]
  have hyq : y ^ q = (y ^ (q / d)) ^ d := by
    rw [← pow_mul, Nat.div_mul_cancel hdq]
  rw [hxp, hyq] at heq
  exact pow_ne_pow_add_one (Nat.one_le_pow _ _ (by omega)) hd2 heq

/-- Reduction to prime exponents: from any solution one obtains a solution with prime
exponents and bases at least as large. -/
