import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

def sifted (N z : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∀ p ∈ sievePrimes z, ¬ p ∣ n * (n + 2))

/-- The number of `1 ≤ n ≤ N` such that every `p ∈ S` divides `n * (n + 2)`. -/
