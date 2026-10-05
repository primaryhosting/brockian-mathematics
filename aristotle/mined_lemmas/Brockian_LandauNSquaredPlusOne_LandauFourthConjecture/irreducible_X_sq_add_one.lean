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
/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- Landau's fourth problem: there are infinitely many primes of the form `n ^ 2 + 1`,
phrased as "for every bound `N` there is some `n > N` with `n ^ 2 + 1` prime". -/

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : Polynomial ℤ) := by
  have hmZ : (X ^ 2 + 1 : Polynomial ℤ).Monic := by monicity!
  refine hmZ.irreducible_of_irreducible_map (Int.castRingHom ℚ) _ ?_
  have hmap : ((X ^ 2 + 1 : Polynomial ℤ).map (Int.castRingHom ℚ)) = (X ^ 2 + 1 : Polynomial ℚ) := by
    simp [Polynomial.map_add, Polynomial.map_pow]
  rw [hmap]
  have hm : (X ^ 2 + 1 : Polynomial ℚ).Monic := by monicity!
  have hd : (X ^ 2 + 1 : Polynomial ℚ).natDegree = 2 := by compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [Polynomial.mem_roots hm.ne_zero] at hx
  have h : x ^ 2 + 1 = 0 := by simpa [IsRoot.def] using hx
  nlinarith [sq_nonneg x]

/-- The polynomial `X ^ 2 + 1` has natural degree `2`. -/
