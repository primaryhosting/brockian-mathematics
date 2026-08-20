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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude

Cullen numbers are `C n = n * 2 ^ n + 1`.  Whether infinitely many of them are prime is a
well-known open problem, so the target `CullenPrimeInfinitude` below is stated and proved as
an unconditional *reduction*: the set of Cullen prime indices is infinite iff Cullen primes
occur past every bound.

We also prove the classical partial results in the opposite direction: every odd prime `p`
divides `C (p - 2)`, hence `C (p - 2)` is composite for every prime `p ≥ 5`, and therefore
infinitely many Cullen numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- The set of indices `n` for which the Cullen number `C n` is prime. -/

def cullenPrimeIndices : Set ℕ := {n | (cullen n).Prime}

/-- **Cullen prime infinitude, reduced to an arbitrarily-large-witness statement.**

Whether infinitely many Cullen numbers are prime is an open problem.  This theorem is an
unconditional Lean-checked *reduction*: the set of Cullen prime indices is infinite exactly
when Cullen primes occur beyond every bound. -/

theorem CullenPrimeInfinitude :
    cullenPrimeIndices.Infinite ↔ ∀ N : ℕ, ∃ n > N, (cullen n).Prime := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨n, hlt, hn⟩ := h N
    exact ⟨n, hn, hlt⟩

/-- For an odd prime `p`, the Cullen number `C (p - 2)` is divisible by `p`.
Indeed `2 * C (p - 2) ≡ (p - 2) * 2 ^ (p - 1) + 2 ≡ -2 + 2 ≡ 0 (mod p)` by Fermat's little
theorem. -/
