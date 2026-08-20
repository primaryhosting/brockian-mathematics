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


open Filter Asymptotics

namespace Brockian
namespace LandauNSquaredPlusOne

/-! ## The statement

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is an open problem, so the main theorem below is a *conditional reduction*: it derives the
conjecture from a Hardy–Littlewood style lower bound for the associated counting function.

Alongside it we prove a number of unconditional results:

* several reformulations of the conjecture (unboundedness of witnesses, unboundedness of the
  counting function, infinitude of the set of primes of the shape `n ^ 2 + 1`);
* the classical congruence restriction on the prime divisors of `n ^ 2 + 1`;
* the unconditional partial result that infinitely many primes divide *some* value `n ^ 2 + 1`.
-/

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/

theorem landauSet_infinite_iff_landauPrimes_infinite :
    LandauSet.Infinite ↔ LandauPrimes.Infinite := by
  constructor
  · intro h
    have hinj : Set.InjOn (fun n : ℕ => n ^ 2 + 1) LandauSet := by
      intro a _ b _ hab
      have h2 : a ^ 2 = b ^ 2 := by simpa using hab
      nlinarith [sq_nonneg (a + b)]
    refine Set.Infinite.mono (s := (fun n : ℕ => n ^ 2 + 1) '' LandauSet) ?_ (h.image hinj)
    rintro p ⟨n, hn, rfl⟩
    exact ⟨hn, ⟨n, rfl⟩⟩
  · intro h
    rw [landauSet_infinite_iff_forall_exists_gt]
    intro N
    obtain ⟨p, ⟨hp, n, rfl⟩, hlt⟩ := h.exists_gt (N ^ 2 + 1)
    refine ⟨n, ?_, hp⟩
    by_contra hle
    push_neg at hle
    have : n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hle 2
    omega

/-! ## Prime divisors of `n ^ 2 + 1` -/

/-- Any odd prime divisor of `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
