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

theorem not_landau_iff :
    ¬ LandauSet.Infinite ↔
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ p ∣ n ^ 2 + 1 := by
  rw [landau_iff_noSmallPrimeFactor, NoSmallPrimeFactorCondition]
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨p, hp, hpn, hdvd⟩ := hN n hn
    exact ⟨p, hp, hpn, hdvd⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨p, hp, hpn, hdvd⟩ := hN n hn
    exact ⟨p, hp, hpn, hdvd⟩

/-- Every prime `p` with `p % 4 ≠ 3` divides some value of the polynomial `X ^ 2 + 1`. -/
