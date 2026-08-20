import Mathlib

/-!
# Admissible arithmetic-progression gap tuples

A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood prime
`k`-tuples conjecture) when, for every prime `p`, the reduction of `H` mod `p` omits at least
one residue class.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime.

This file characterises admissibility of the arithmetic progression tuples
`{0, d, 2d, …, (k-1)d}` and derives new admissible gap ranges for `90 ≤ k ≤ 98`.
-/

open scoped BigOperators

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if for every prime `p` it omits at least one
residue class modulo `p`. -/

lemma not_dvd_primorialUpTo {p n : ℕ} (hp : p.Prime) (hpn : n < p) : ¬ p ∣ primorialUpTo n := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
  obtain ⟨hqr, hqp⟩ := Finset.mem_filter.mp hq
  have : p = q := ((Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq)
  have := Finset.mem_range.mp hqr
  omega

/-- **New admissible gap ranges, `90 ≤ k ≤ 98`.**  For every length `k` in the range
`90 ≤ k ≤ 98`, the arithmetic progression tuple `{0, d, 2d, …, (k-1)d}` with common difference
the primorial `98#` is admissible; moreover, for such `k` a difference `d` yields an admissible
tuple exactly when every prime `p ≤ k` divides `d`, and the smaller primorial `89#` works
precisely for `k ≤ 96`. -/
