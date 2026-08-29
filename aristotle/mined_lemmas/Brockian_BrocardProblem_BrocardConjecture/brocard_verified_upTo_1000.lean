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
import Brockian.BrocardProblem

/-!
# Brocard's problem, in Mathlib's vocabulary

`Brockian/BrocardProblem.lean` is import-free (so that the required header
comment can be its first line), and therefore defines factorial itself as
`Brockian.BrocardProblem.fact`.  Here we check that `fact` agrees with Mathlib's
`Nat.factorial` and restate the two main results using `Nat.factorial`.
-/

namespace Brockian.BrocardProblem

open Nat

/-- The self-contained factorial of `Brockian/BrocardProblem.lean` agrees with
Mathlib's `Nat.factorial`. -/

theorem brocard_verified_upTo_1000 {n m : Nat} (hn : n ≤ 1000) (h : fact n + 1 = m ^ 2) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  by_cases h8 : n ≤ 7
  · exact brocard_small h8 h
  · exact absurd h (not_sq_of_certificate (certificate_of_le_1000 (by omega) hn) m)

/-- **Brocard's conjecture, conditionally.**  If every `n > 1000` admits a
modular non-residue certificate for `n ! + 1`, then the only solutions of
`n ! + 1 = m ^ 2` are `n = 4, 5, 7`.  The range `n ≤ 1000` is verified
unconditionally, so the hypothesis is only about `n > 1000`. -/
