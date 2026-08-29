import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

def twins (N : ℕ) : Finset ℕ := (range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)

/-- The integers `1 ≤ n ≤ N` such that `n * (n + 2)` has no prime factor among `sievePrimes z`. -/
