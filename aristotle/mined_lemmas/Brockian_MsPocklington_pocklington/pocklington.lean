import Mathlib
namespace Brockian.MsPocklington

/-- If `p` is a prime divisor of `N` and `gcd (a ^ m - 1) N = 1`, then `a ^ m ≢ 1 (mod p)`. -/

theorem pocklington (N q m : ℕ) (hN : 1 < N) (hfac : N - 1 = q * m) (hq : q.Prime)
    (hqbig : N < q * q) (a : ℕ)
    (h1 : a ^ (N - 1) ≡ 1 [MOD N])
    (h2 : Nat.gcd (a ^ ((N - 1) / q) - 1) N = 1) :
    N.Prime := by
  have hq0 : 0 < q := hq.pos
  have hm : (N - 1) / q = m := by
    rw [hfac, Nat.mul_div_cancel_left _ hq0]
  rw [hm] at h2
  by_contra hnp
  have hNpos : 0 < N := by omega
  have hmin : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self hNpos hnp
  have hpp : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hlt : q < N.minFac := q_lt_prime_divisor hfac hq h1 h2 hpp (Nat.minFac_dvd N)
  nlinarith [hmin, hlt, sq_nonneg (N.minFac)]

end Brockian.MsPocklington

