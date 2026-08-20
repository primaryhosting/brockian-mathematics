import Mathlib
namespace Brockian.MsPocklington

/-- If `p` is a prime divisor of `N` and `gcd (a ^ m - 1) N = 1`, then `a ^ m ≢ 1 (mod p)`. -/

private lemma q_lt_prime_divisor {N q m a p : ℕ} (hfac : N - 1 = q * m)
    (hq : q.Prime) (h1 : a ^ (N - 1) ≡ 1 [MOD N]) (h2 : Nat.gcd (a ^ m - 1) N = 1)
    (hp : p.Prime) (hpN : p ∣ N) : q < p := by
  have hd : q ∣ p - 1 := q_dvd_prime_sub_one hfac hq h1 h2 hp hpN
  have hp2 : 2 ≤ p := hp.two_le
  have hpos : 0 < p - 1 := by omega
  have := Nat.le_of_dvd hpos hd
  omega

/-- Pocklington's primality criterion: if N−1 = q·m with q prime, q > √N, and there is a with
    a^(N−1) ≡ 1 (mod N) and gcd(a^((N−1)/q) − 1, N) = 1, then N is prime. -/
