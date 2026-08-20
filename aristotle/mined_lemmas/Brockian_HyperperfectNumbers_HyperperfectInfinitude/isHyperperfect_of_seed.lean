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

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigma1 n` is the sum of all divisors of `n`. -/

theorem isHyperperfect_of_seed {m : ℕ} (h : HyperperfectSeed m) :
    IsHyperperfect ((m + 1) * (m * m + m + 1)) :=
  ⟨m, isKHyperperfect_of_seed h⟩

/-!
## The Brockian conjecture on hyperperfect numbers

Whether there are infinitely many hyperperfect numbers is open (it already contains the
infinitude of perfect numbers, which are exactly the `1`-hyperperfect numbers, as a special
case).  What follows is a Lean-checked *conditional reduction*: the infinitude of hyperperfect
numbers follows from the (conjectural, but Bunyakovsky/Schinzel-type) statement that there are
infinitely many `m` for which `m + 1` and `m² + m + 1` are both prime.
-/

/-- **Conditional infinitude of hyperperfect numbers.**  If there are infinitely many `m` such
that `m + 1` and `m * m + m + 1` are both prime, then there are infinitely many hyperperfect
numbers. -/
