import Mathlib
namespace C6.NT8

/-- Gauss's identity: the sum of `φ(d)` over the divisors `d` of `n` equals `n`.
The hypothesis `0 < n` is part of the requested statement; it turns out to be
unnecessary, since Mathlib's `Nat.sum_totient` also covers `n = 0`. -/

theorem prime_dvd_factorial (p n : ℕ) (hp : p.Prime) (h : p ≤ n) : p ∣ n.factorial :=
  Nat.dvd_factorial hp.pos h

/-- Euler's theorem: if `a` is coprime to `n`, then `a ^ φ(n) ≡ 1 [MOD n]`. -/
