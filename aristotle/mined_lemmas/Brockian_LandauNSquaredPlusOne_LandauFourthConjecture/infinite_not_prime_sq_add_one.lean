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

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

open Zsqrtd

/-- A *Landau prime* is a prime natural number of the form `n ^ 2 + 1`. -/

theorem infinite_not_prime_sq_add_one :
    {n : ℕ | ¬ Nat.Prime (n ^ 2 + 1)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨5 * (a + 1) + 2, ?_, by omega⟩
  have hfac : (5 * (a + 1) + 2) ^ 2 + 1 = 5 * (5 * (a + 1) ^ 2 + 4 * (a + 1) + 1) := by ring
  simp only [Set.mem_setOf_eq, hfac]
  exact Nat.not_prime_mul (by norm_num) (by nlinarith)

/-- Sanity check: the first few Landau primes. -/
example : IsLandauPrime 2 := ⟨by norm_num, 1, by norm_num⟩
example : IsLandauPrime 5 := ⟨by norm_num, 2, by norm_num⟩
example : IsLandauPrime 17 := ⟨by norm_num, 4, by norm_num⟩
example : IsLandauPrime 101 := ⟨by norm_num, 10, by norm_num⟩

end Brockian.LandauNSquaredPlusOne

