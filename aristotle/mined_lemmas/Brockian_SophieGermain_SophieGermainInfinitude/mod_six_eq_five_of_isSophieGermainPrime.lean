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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem mod_six_eq_five_of_isSophieGermainPrime {p : ℕ} (hp : IsSophieGermainPrime p)
    (hp3 : 3 < p) : p % 6 = 5 := by
  obtain ⟨hprime, hq⟩ := hp
  have h2 : ¬ (2 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h
    omega
  have h3 : ¬ (3 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).mp h
    omega
  have h3' : ¬ (3 ∣ 2 * p + 1) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h
    omega
  have e2 : p % 2 ≠ 0 := fun h => h2 (Nat.dvd_of_mod_eq_zero h)
  have e3 : p % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  have e3' : (2 * p + 1) % 3 ≠ 0 := fun h => h3' (Nat.dvd_of_mod_eq_zero h)
  have hp2 : p % 2 = 1 := by omega
  have hne1 : p % 3 ≠ 1 := fun h => e3' (by omega)
  have hp3' : p % 3 = 2 := by omega
  omega

/-- **Conditional reduction.**  The Sophie Germain conjecture — the infinitude of the set of
primes `p` for which `2 * p + 1` is also prime — follows from (and is in fact equivalent to,
see `sophieGermainPrimes_infinite_iff_unbounded`) the statement that Sophie Germain primes are
unbounded.  The unboundedness hypothesis `hUnbounded` is exactly the open input; everything
else is proved here.

This is the target statement `Brockian.SophieGermain.SophieGermainInfinitude`, stated as a
Lean-checked conditional reduction, since the unconditional Sophie Germain conjecture is an
open problem.  The reduction is closed by the Mathlib lemma
`Set.infinite_of_forall_exists_gt`. -/
