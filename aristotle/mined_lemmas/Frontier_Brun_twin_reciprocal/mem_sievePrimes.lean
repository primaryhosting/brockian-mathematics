import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

lemma mem_sievePrimes {z p : ℕ} : p ∈ sievePrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [sievePrimes, Nat.lt_succ_iff, and_comm]

