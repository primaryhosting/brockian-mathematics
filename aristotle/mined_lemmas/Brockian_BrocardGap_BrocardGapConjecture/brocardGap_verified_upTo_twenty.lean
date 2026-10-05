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

open scoped Nat

namespace Brockian.BrocardGap

/-! ### Elementary facts about perfect squares -/

/-- If `k` lies strictly between two consecutive squares, it is not a square. -/

theorem brocardGap_verified_upTo_twenty (n m : ℕ) (h8 : 8 ≤ n) (h20 : n ≤ 20) :
    n ! + 1 ≠ m ^ 2 := by
  interval_cases n
  · exact not_sq_of_between (a := 200) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 602) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 1904) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 6317) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 21886) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 78911) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 295259) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 1143535) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 4574143) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 18859677) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 80014834) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 348776576) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 1559776268) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m

/-! ### The classification of Brocard solutions -/

/-- **Brocard Gap Conjecture (conditional reduction).**
Granting the Brocard gap hypothesis — that `n ! + 1` is not a perfect square for `n ≥ 8` —
the equation `n ! + 1 = m ^ 2` has exactly the three solutions
`(n, m) = (4, 5), (5, 11), (7, 71)`.

The proof splits on the hypothesis `8 ≤ n`: the finitely many cases `n ≤ 7` are settled
unconditionally, and the remaining branch is exactly the assumed gap hypothesis. -/
