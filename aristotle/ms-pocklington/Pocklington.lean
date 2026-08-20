import Mathlib
namespace Brockian.MsPocklington
/-- Pocklington's primality criterion: if N−1 = q·m with q prime, q > √N, and there is a with
    a^(N−1) ≡ 1 (mod N) and gcd(a^((N−1)/q) − 1, N) = 1, then N is prime. -/
theorem pocklington (N q m : ℕ) (hN : 1 < N) (hfac : N - 1 = q * m) (hq : q.Prime)
    (hqbig : N < q * q) (a : ℕ)
    (h1 : a ^ (N - 1) ≡ 1 [MOD N])
    (h2 : Nat.gcd (a ^ ((N - 1) / q) - 1) N = 1) :
    N.Prime := by
  sorry
end Brockian.MsPocklington
