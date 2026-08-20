import Mathlib
namespace C6.NT8

/-- Gauss's identity: the sum of `φ(d)` over the divisors `d` of `n` equals `n`.
The hypothesis `0 < n` is part of the requested statement; it turns out to be
unnecessary, since Mathlib's `Nat.sum_totient` also covers `n = 0`. -/

theorem coprime_totient (n : ℕ) (a : ℕ) (h : Nat.Coprime a n) : a^(Nat.totient n) ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

end C6.NT8

