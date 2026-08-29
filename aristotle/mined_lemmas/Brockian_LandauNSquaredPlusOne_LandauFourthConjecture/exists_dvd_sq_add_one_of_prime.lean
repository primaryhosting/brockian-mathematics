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

theorem exists_dvd_sq_add_one_of_prime {p : ℕ} (hp : p.Prime) (h4 : p % 4 ≠ 3) :
    ∃ n : ℕ, p ∣ n ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr h4
  refine ⟨a.val, ?_⟩
  have hz : ((a.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, sq, ← ha]
    ring
  exact (ZMod.natCast_eq_zero_iff (a.val ^ 2 + 1) p).mp hz

/-- **Unconditional partial result.**  Infinitely many primes divide some value of
`n ^ 2 + 1`.  (The open conjecture asks for infinitely many primes that are *equal* to
some `n ^ 2 + 1`.) -/
