import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

lemma sievePrimes_odd {z p : ℕ} (hp : p ∈ sievePrimes z) : Odd p := by
  rw [mem_sievePrimes] at hp
  exact hp.2.1.odd_of_ne_two hp.2.2

