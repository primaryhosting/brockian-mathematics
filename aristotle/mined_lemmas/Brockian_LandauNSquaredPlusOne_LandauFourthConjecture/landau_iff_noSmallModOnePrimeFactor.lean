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

theorem landau_iff_noSmallModOnePrimeFactor :
    LandauSet.Infinite ↔ NoSmallModOnePrimeFactorCondition := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hgt⟩ := Set.infinite_iff_exists_gt.mp hinf (max N 1)
    refine ⟨n, lt_of_le_of_lt (le_max_left N 1) hgt,
      even_of_prime_sq_add_one (lt_of_le_of_lt (le_max_right N 1) hgt) hn, ?_⟩
    intro p hpp _ hpn
    exact no_small_prime_factor_of_prime hn p hpp hpn
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hgt, heven, hn⟩ := h (max N 1)
    have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hgt)
    refine ⟨n, prime_of_no_small_prime_factor hn1 ?_, lt_of_le_of_lt (le_max_left N 1) hgt⟩
    intro p hpp hpn hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := heven
      have h2 : (2 : ℕ) ∣ n ^ 2 := ⟨2 * k ^ 2, by subst hk; ring⟩
      omega
    exact hn p hpp (prime_mod_four_eq_one_of_dvd_sq_add_one hpp hp2 hdvd) hpn hdvd

/-- Small members of `LandauSet`: for `n = 1, 2, 4, 6, 10, 14, 16, 20` the numbers
`2, 5, 17, 37, 101, 197, 257, 401` are prime. -/
