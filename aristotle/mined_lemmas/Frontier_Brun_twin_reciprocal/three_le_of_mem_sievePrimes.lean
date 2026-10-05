import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

lemma three_le_of_mem_sievePrimes {z p : ℕ} (hp : p ∈ sievePrimes z) : 3 ≤ p := by
  rw [mem_sievePrimes] at hp
  rcases hp with ⟨-, hp, h2⟩
  have := hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · interval_cases p <;> simp_all
  · exact h

end Brun

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

