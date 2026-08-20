import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma pepin_mpr (n : ℕ) (hn : 1 ≤ n)
    (h : (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1) :
    (2 ^ (2 ^ n) + 1).Prime :=
  lucas_primality (2 ^ (2 ^ n) + 1) 3 (pow_fermat_sub_one n h)
    (pow_prime_div_ne_one n hn h)

/-- Pépin's test: the Fermat number F_n = 2^(2^n)+1 (n ≥ 1) is prime iff
    3^((F_n−1)/2) ≡ −1 (mod F_n). -/
