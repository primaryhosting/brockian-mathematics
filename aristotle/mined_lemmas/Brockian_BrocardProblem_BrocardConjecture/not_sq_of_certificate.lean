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

theorem not_sq_of_certificate {n : Nat} (h : HasCertificate n) (m : Nat) :
    fact n + 1 ≠ m ^ 2 := by
  obtain ⟨p, hp, hx⟩ := h
  exact ne_sq_of_mod_witness hp hx m

/-! ### The certificate table for `8 ≤ n ≤ 1000` -/

/-- `witTable` lists, for `n = 8, 9, …, 1000` (in this order), a pair `(p, r)`
where `p` is a prime larger than `n` modulo which `n ! + 1` is a quadratic
non-residue, and `r = (n ! + 1) % p`. -/
