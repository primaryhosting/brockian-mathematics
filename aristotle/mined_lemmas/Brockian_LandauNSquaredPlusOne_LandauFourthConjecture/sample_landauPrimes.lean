import Brockian.LandauNSquaredPlusOne

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

namespace Brockian.LandauNSquaredPlusOne

open Set

/-- The set of primes of the form `n ^ 2 + 1` (the "Landau primes"). -/

theorem sample_landauPrimes :
    ({2, 5, 17, 37, 101, 197, 257, 401} : Set ℕ) ⊆ LandauPrimes := by
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨by norm_num, 1, by norm_num⟩
  · exact ⟨by norm_num, 2, by norm_num⟩
  · exact ⟨by norm_num, 4, by norm_num⟩
  · exact ⟨by norm_num, 6, by norm_num⟩
  · exact ⟨by norm_num, 10, by norm_num⟩
  · exact ⟨by norm_num, 14, by norm_num⟩
  · exact ⟨by norm_num, 16, by norm_num⟩
  · exact ⟨by norm_num, 20, by norm_num⟩

end Brockian.LandauNSquaredPlusOne

