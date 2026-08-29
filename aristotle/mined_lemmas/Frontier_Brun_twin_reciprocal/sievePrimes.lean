import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

def sievePrimes (z : ℕ) : Finset ℕ := (range (z + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The twin primes `p ≤ N` (i.e. `p` and `p + 2` are both prime). -/
