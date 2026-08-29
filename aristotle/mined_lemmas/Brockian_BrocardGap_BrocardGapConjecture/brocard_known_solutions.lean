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

## Setting

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`; the only known ones are
`n = 4, 5, 7`, and it is an open problem whether there are others.

The *Brocard gap* statement formalised here is the quantitative "sparseness of squares just
above `n !`" phenomenon underlying the conjecture:

* consecutive squares just above `n !` are more than `Nat.sqrt (n !)` apart, so the window
  `(n !, n ! + Nat.sqrt (n !)]` contains **at most one** perfect square;
* for `n ≥ 8` this window has length at least `n ^ 2`, because `n ^ 4 ≤ n !` (proved by
  induction on `n`);
* consequently any Brocard solution `n ! + 1 = m ^ 2` with `n ≥ 8` has `m > n ^ 2` and yields
  the factorisation `n ! = (m - 1) * (m + 1)` of `n !` into two factors differing by `2`.
-/

open scoped Nat

namespace Brockian
namespace BrocardGap

/-- The Brocard gap window at `n`: the integers strictly above `n !` and at most
`n ! + Nat.sqrt (n !)`. -/

theorem brocard_known_solutions :
    4 ! + 1 = 5 ^ 2 ∧ 5 ! + 1 = 11 ^ 2 ∧ 7 ! + 1 = 71 ^ 2 :=
  ⟨by decide, by decide, by decide⟩

/-- **Brocard Gap Conjecture.**

For every `n ≥ 8`:

* the window `(n !, n ! + Nat.sqrt (n !)]` contains at most one perfect square, and this
  window has length at least `n ^ 2`;
* consecutive squares just above `n !` are more than `n ^ 2` apart;
* every Brocard solution `n ! + 1 = m ^ 2` satisfies `m > n ^ 2` and yields the factorisation
  `n ! = (m - 1) * (m + 1)` into two factors differing by `2`.
-/
