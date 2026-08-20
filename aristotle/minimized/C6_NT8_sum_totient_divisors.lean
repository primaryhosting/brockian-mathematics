import Mathlib
namespace C6.NT8

/-- Gauss's identity: the sum of `φ(d)` over the divisors `d` of `n` equals `n`.
The hypothesis `0 < n` is part of the requested statement; it turns out to be
unnecessary, since Mathlib's `Nat.sum_totient` also covers `n = 0`. -/

theorem sum_totient_divisors (n : ℕ) (hn : 0 < n) : ∑ d ∈ Nat.divisors n, Nat.totient d = n :=
  Nat.sum_totient n

/-- A prime `p ≤ n` divides `n !`. -/
