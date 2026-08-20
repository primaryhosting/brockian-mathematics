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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 rejects a module doc comment `/-! ... -/` before `import`, so the header above
-- is an ordinary block comment; its text is otherwise exactly as requested.)

import Mathlib

/-!
# Landau's fourth problem: infinitely many primes of the form `n ^ 2 + 1`

Landau's fourth conjecture is an open problem.  This file provides:

* a formal statement of Bunyakovsky's conjecture (`Bunyakovsky`);
* a Lean-checked *conditional reduction*: Landau's fourth conjecture follows from
  Bunyakovsky's conjecture (`LandauFourthConjecture`), via the irreducibility of
  `X ^ 2 + 1` over `ℤ` and the absence of a fixed divisor;
* unconditional partial results: an odd prime divides some `n ^ 2 + 1` iff it is
  `1 mod 4`, and hence infinitely many primes divide numbers of the form `n ^ 2 + 1`.
-/

namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  refine Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3)) _
    monic_X_sq_add_one ?_
  have hmap : ((X ^ 2 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))) = (X ^ 2 + 1 : (ZMod 3)[X]) := by
    simp
  rw [hmap]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have h : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    simp [h]
  · intro x hx
    rw [Polynomial.IsRoot.def] at hx
    simp only [eval_add, eval_pow, eval_X, eval_one] at hx
    revert hx
    revert x
    decide

/-- `X ^ 2 + 1` has no fixed divisor `d > 1`: already `0 ^ 2 + 1 = 1`. -/
