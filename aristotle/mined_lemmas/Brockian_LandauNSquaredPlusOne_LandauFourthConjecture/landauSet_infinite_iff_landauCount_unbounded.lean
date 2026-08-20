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

theorem landauSet_infinite_iff_landauCount_unbounded :
    LandauSet.Infinite ↔ ∀ M : ℕ, ∃ N : ℕ, M < landauCount N := by
  constructor
  · intro h M
    obtain ⟨s, hs, hcard⟩ := h.exists_subset_card_eq (M + 1)
    obtain ⟨N, hN⟩ := s.exists_nat_subset_range
    refine ⟨N, ?_⟩
    have hsub : s ⊆ (Finset.range N).filter fun n => Nat.Prime (n ^ 2 + 1) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hN hx, hs hx⟩
    have := Finset.card_le_card hsub
    simp only [landauCount]
    omega
  · intro h hfin
    obtain ⟨N, hN⟩ := h hfin.toFinset.card
    have hsub : ((Finset.range N).filter fun n => Nat.Prime (n ^ 2 + 1)) ⊆ hfin.toFinset := by
      intro x hx
      exact hfin.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
    have := Finset.card_le_card hsub
    simp only [landauCount] at hN
    omega

/-- Landau's fourth conjecture is equivalent to the infinitude of the set of primes of the
form `n ^ 2 + 1`. -/
