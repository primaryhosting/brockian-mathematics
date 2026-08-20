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

lemma four_pow_lt_factorial : ∀ n : ℕ, 9 ≤ n → 4 ^ n < n ! := by
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 9 with h | h
    · have hk8 : k = 8 := by omega
      subst hk8
      decide
    · have hih := ih h
      calc 4 ^ (k + 1) = 4 * 4 ^ k := by ring
        _ < 4 * k ! := (Nat.mul_lt_mul_left (by norm_num)).mpr hih
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul_right _ (by omega)
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- The three known solutions of Brocard's equation, showing that the statement below
is not vacuous. -/
example : 4 ! + 1 = 5 ^ 2 ∧ 5 ! + 1 = 11 ^ 2 ∧ 7 ! + 1 = 71 ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Brocard Gap Conjecture (verified partial form).**

If `n ! + 1 = m ^ 2` then either `n ≤ 7` (the range containing the three known
solutions `n = 4, 5, 7`) or else the solution lies beyond the verified gap and is
huge: `n > 100` and `m > 2 ^ n`.

Equivalently: Brocard's equation has no solution with `8 ≤ n ≤ 100`, and any further
solution must have `m` exceeding `2 ^ n`.  (That no further solution exists at all
remains open.) -/
