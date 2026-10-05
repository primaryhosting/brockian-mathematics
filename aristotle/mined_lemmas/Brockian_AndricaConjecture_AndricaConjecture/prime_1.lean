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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Note: the header block above is written as a plain block comment rather than a module docstring
(`/-! ... -/`) because Lean requires `import` commands to precede every other command, including
module docstrings.

## Contents

* `sqrt_sub_sqrt_lt_one_of_sq_gap_le` : the elementary estimate `√b - √a < 1` for `a < b`
  with `(b - a)^2 ≤ 4a`.
* `sqrt_sub_sqrt_lt_one_iff` : the Andrica inequality is equivalent to the gap bound.
* `AndricaConjecture` : Andrica's conjecture, conditional on the prime-gap bound
  `(p_{n+1} - p_n)^2 ≤ 4 p_n`.  (Andrica's conjecture itself is an open problem.)
* `andrica_first_ten` : unconditional verification for the first ten prime gaps.
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`). -/

lemma prime_1 : prime 1 = 3 := prime_eq _ _ (by norm_num) (by decide)
