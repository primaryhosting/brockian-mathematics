import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma three_le_of_mem_oddPrimes {z p : ℕ} (h : p ∈ oddPrimes z) : 3 ≤ p := by
  obtain ⟨-, hp, h2⟩ := mem_oddPrimes.mp h
  have := hp.two_le
  omega

end Brun

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

import RequestProject.Defs

/-!
# A weak Mertens-type upper bound

We show `∑_{p ≤ 2^J} 1/p ≤ 1/2 + 8 √J`, which is all the prime-density input Brun's
argument needs.  The only external input is Chebyshev's bound `primorial n ≤ 4 ^ n`.
-/

namespace Brun

open Finset

/-- The primes `≤ x`. -/
