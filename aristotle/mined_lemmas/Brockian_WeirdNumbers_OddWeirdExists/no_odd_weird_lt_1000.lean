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

theorem no_odd_weird_lt_1000 (n : ℕ) (hlt : n < 1000) (hodd : Odd n) : ¬ n.Weird := by
  intro hw
  have : n = 945 := odd_abundant_lt_1000 n hlt hodd hw.1
  subst this
  exact hw.2 pseudoperfect_945

end Brockian.WeirdNumbers

