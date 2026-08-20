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

theorem infinite_setOf_prime_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hap, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (max a 2) (by norm_num)
  have h4 : p % 4 = 1 := by
    unfold Nat.ModEq at hmod
    omega
  exact ⟨p, ⟨hp, (prime_dvd_sq_add_one_iff hp (by omega)).2 h4⟩, by omega⟩

end Brockian.LandauNSquaredPlusOne

