import Mathlib
namespace C2.BSieve3

noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ)/p) / ((1 - 1/(p:ℝ))^G.card) else 1

/-- The local factor of the admissible 8-tuple `{0,2,6,8,12,18,20,26}` is positive at
every `p`.  For non-primes the factor is `1`; for primes one checks `ν(p) < p`
directly for `p ≤ 8` and uses `ν(p) ≤ |G| = 8 < p` otherwise. -/
