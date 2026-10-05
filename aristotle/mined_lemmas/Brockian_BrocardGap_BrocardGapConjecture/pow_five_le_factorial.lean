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

theorem pow_five_le_factorial : ∀ n : ℕ, 8 ≤ n → n ^ 5 ≤ n ! := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 8 with hk | hk
    · have hk8 : k + 1 = 8 := by omega
      rw [hk8]
      decide
    · have hk' : k ^ 5 ≤ k ! := ih hk
      have hstep : (k + 1) ^ 4 ≤ k ^ 5 := by
        have h1 : (8 * (k + 1)) ^ 4 ≤ (9 * k) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        have e1 : (8 * (k + 1)) ^ 4 = 4096 * (k + 1) ^ 4 := by ring
        have e2 : (9 * k) ^ 4 = 6561 * k ^ 4 := by ring
        rw [e1, e2] at h1
        have h2 : 6561 * k ^ 4 ≤ 4096 * k ^ 5 := by
          have hc : 6561 ≤ 4096 * k := by omega
          calc 6561 * k ^ 4 ≤ (4096 * k) * k ^ 4 := Nat.mul_le_mul_right _ hc
            _ = 4096 * k ^ 5 := by ring
        exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by norm_num)
      calc (k + 1) ^ 5 = (k + 1) * (k + 1) ^ 4 := by ring
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul_left _ (hstep.trans hk')
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- `n ^ 4 ≤ n !` for `n ≥ 8`. -/
