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

/-
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block comment
-- and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.WeirdNumbers

/-! ## Setup

We use Mathlib's `Nat.Weird`: `n` is weird if it is *abundant*
(`n < ∑ i ∈ n.properDivisors, i`) but not *pseudoperfect* (no subset of its proper divisors
sums to `n`).

The statement "there exists an odd weird number" is an open problem, so the target
`OddWeirdExists` is formalised as a **conditional reduction**: from a verifiable criterion on a
single odd number we deduce the existence of an odd weird number.  The criterion involves the
*abundance* `∑ i ∈ n.properDivisors, i - n`, which is typically far smaller than `n`, so it is a
genuine reduction of the search problem.
-/

/-- The abundance of `n`: the sum of the proper divisors of `n` minus `n` (truncated
subtraction). -/

theorem weird_iff {n : ℕ} (hn : 0 < n) :
    n.Weird ↔ n.Abundant ∧ ∀ s ⊆ n.properDivisors, ∑ i ∈ s, i ≠ abundance n := by
  constructor
  · rintro ⟨hab, hp⟩
    refine ⟨hab, fun s hs hsum => hp ?_⟩
    exact pseudoperfect_of_exists_subset_sum_eq_abundance hn hab ⟨s, hs, hsum⟩
  · rintro ⟨hab, h⟩
    refine ⟨hab, fun hp => ?_⟩
    obtain ⟨s, hs, hsum⟩ := exists_subset_sum_eq_abundance_of_pseudoperfect hp
    exact h s hs hsum

/-! ## The target: a conditional reduction -/

/-- **Odd weird exists (conditional reduction).**  If `n` is an odd abundant number such that no
subset of its proper divisors sums to its abundance `∑ i ∈ n.properDivisors, i - n`, then an odd
weird number exists.

The existence of an odd weird number is an open problem; this theorem reduces it to the
(much smaller) search for a representation of the abundance. -/
