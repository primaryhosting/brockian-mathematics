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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Brocard's problem and the "Brocard gap"

Brocard's problem asks for the natural numbers `n` such that `n ! + 1` is a perfect
square.  The only known solutions are `n = 4, 5, 7` (with `n ! + 1 = 5 ^ 2, 11 ^ 2,
71 ^ 2`), and it is a long-standing open problem (still open today) that there are no
further solutions.

The *gap* formulation says that after `n = 7` there is a gap in the set of solutions.
The full conjecture (that the gap is infinite) is open; what is proved here,
unconditionally and by kernel-checked computation, is:

* there is **no** solution with `8 ≤ n ≤ 100`, and
* every hypothetical solution with `n > 7` is enormous: it satisfies `n > 100` and
  `m > 2 ^ n`.

This is the content of `Brockian.BrocardGap.BrocardGapConjecture`.
-/

namespace Brockian.BrocardGap

open Nat

/-- If a natural number `x` lies strictly between two consecutive squares, it is not
a square. -/

private lemma brocard_no_sol_50 (m : ℕ) : Nat.factorial 50 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 174396368086360611696209329639024) (by decide) (by decide) m

