import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma pow_prime_div_ne_one (n : ℕ) (hn : 1 ≤ n)
    (h : (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1) :
    ∀ q : ℕ, q.Prime → q ∣ (2 ^ (2 ^ n) + 1 - 1) →
      (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ ((2 ^ (2 ^ n) + 1 - 1) / q) ≠ 1 := by
  intro q hq hdiv
  -- q divides 2^(2^n), so q = 2
  have hq2 : q = 2 := by
    have hdvd2pow : q ∣ 2 ^ (2 ^ n) := by simpa using hdiv
    have hdvd2 : q ∣ 2 := hq.dvd_of_dvd_pow hdvd2pow
    have := Nat.le_of_dvd (by norm_num) hdvd2
    interval_cases q <;> trivial
  rw [hq2]
  -- Now the exponent is 2^(2^n) / 2
  simp_all
  exact neg_one_ne_one_fermat n hn

/-- Backward direction of Pépin's test (Lucas primality with witness `3`). -/
