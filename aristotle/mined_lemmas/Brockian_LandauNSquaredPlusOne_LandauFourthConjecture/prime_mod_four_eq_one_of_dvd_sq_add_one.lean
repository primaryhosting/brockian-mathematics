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

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime.
Landau's fourth problem asserts that this set is infinite; it is open. -/

theorem prime_mod_four_eq_one_of_dvd_sq_add_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(n : ZMod p), ?_⟩
    have hz : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at hz
    linear_combination -hz
  have h3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  omega

/-- If `n ^ 2 + 1` is prime and `n > 1`, then `n` is even. -/
