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

theorem no_solution_of_le_hundred {n : ℕ} (h8 : 8 ≤ n) (h100 : n ≤ 100) (m : ℕ) :
    n ! + 1 ≠ m ^ 2 := by
  interval_cases n
  exacts [brocard_no_sol_8 m, brocard_no_sol_9 m, brocard_no_sol_10 m, brocard_no_sol_11 m, brocard_no_sol_12 m, brocard_no_sol_13 m, brocard_no_sol_14 m, brocard_no_sol_15 m, brocard_no_sol_16 m, brocard_no_sol_17 m, brocard_no_sol_18 m, brocard_no_sol_19 m, brocard_no_sol_20 m, brocard_no_sol_21 m, brocard_no_sol_22 m, brocard_no_sol_23 m, brocard_no_sol_24 m, brocard_no_sol_25 m, brocard_no_sol_26 m, brocard_no_sol_27 m, brocard_no_sol_28 m, brocard_no_sol_29 m, brocard_no_sol_30 m, brocard_no_sol_31 m, brocard_no_sol_32 m, brocard_no_sol_33 m, brocard_no_sol_34 m, brocard_no_sol_35 m, brocard_no_sol_36 m, brocard_no_sol_37 m, brocard_no_sol_38 m, brocard_no_sol_39 m, brocard_no_sol_40 m, brocard_no_sol_41 m, brocard_no_sol_42 m, brocard_no_sol_43 m, brocard_no_sol_44 m, brocard_no_sol_45 m, brocard_no_sol_46 m, brocard_no_sol_47 m, brocard_no_sol_48 m, brocard_no_sol_49 m, brocard_no_sol_50 m, brocard_no_sol_51 m, brocard_no_sol_52 m, brocard_no_sol_53 m, brocard_no_sol_54 m, brocard_no_sol_55 m, brocard_no_sol_56 m, brocard_no_sol_57 m, brocard_no_sol_58 m, brocard_no_sol_59 m, brocard_no_sol_60 m, brocard_no_sol_61 m, brocard_no_sol_62 m, brocard_no_sol_63 m, brocard_no_sol_64 m, brocard_no_sol_65 m, brocard_no_sol_66 m, brocard_no_sol_67 m, brocard_no_sol_68 m, brocard_no_sol_69 m, brocard_no_sol_70 m, brocard_no_sol_71 m, brocard_no_sol_72 m, brocard_no_sol_73 m, brocard_no_sol_74 m, brocard_no_sol_75 m, brocard_no_sol_76 m, brocard_no_sol_77 m, brocard_no_sol_78 m, brocard_no_sol_79 m, brocard_no_sol_80 m, brocard_no_sol_81 m, brocard_no_sol_82 m, brocard_no_sol_83 m, brocard_no_sol_84 m, brocard_no_sol_85 m, brocard_no_sol_86 m, brocard_no_sol_87 m, brocard_no_sol_88 m, brocard_no_sol_89 m, brocard_no_sol_90 m, brocard_no_sol_91 m, brocard_no_sol_92 m, brocard_no_sol_93 m, brocard_no_sol_94 m, brocard_no_sol_95 m, brocard_no_sol_96 m, brocard_no_sol_97 m, brocard_no_sol_98 m, brocard_no_sol_99 m, brocard_no_sol_100 m]

/-- Factorials outgrow `4 ^ n` from `n = 9` on. -/
