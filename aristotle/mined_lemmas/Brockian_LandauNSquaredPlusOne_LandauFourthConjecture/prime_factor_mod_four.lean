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

namespace Brockian
namespace LandauNSquaredPlusOne

open Set

/-- The set of natural numbers `n` for which `n ^ 2 + 1` is prime. -/

theorem prime_factor_mod_four {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ n ^ 2 + 1) :
    p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : ((n : ZMod p)) ^ 2 = -1 := by
    have : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at this
    linear_combination this
  have h3 : p % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  omega

/-! ### An unconditional partial result -/

/-- Unconditionally, infinitely many primes divide some number of the form `n ^ 2 + 1`.
(Equivalently, infinitely many primes `p` have `-1` as a quadratic residue.) -/
