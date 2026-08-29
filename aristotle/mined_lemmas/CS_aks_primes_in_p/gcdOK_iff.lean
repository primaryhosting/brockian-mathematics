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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem gcdOK_iff (n r : ℕ) :
    gcdOK n r = true ↔ ∀ a, 2 ≤ a → a ≤ r → Nat.gcd a n = 1 ∨ Nat.gcd a n = n := by
  simp only [gcdOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  constructor
  · intro h a ha2 har
    rcases h a (by omega) with (h1 | h1) | h1
    · omega
    · exact Or.inl h1
    · exact Or.inr h1
  · intro h a ha
    rcases Nat.lt_or_ge a 2 with h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases h a h1 (by omega) with h2 | h2
      · exact Or.inl (Or.inr h2)
      · exact Or.inr h2

/-- The polynomial congruence test for a single `a`. -/
