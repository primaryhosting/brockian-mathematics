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


theorem ordOK_iff (n r K : ℕ) :
    ordOK n r K = true ↔ ∀ i, 1 ≤ i → i ≤ K → n ^ i % r ≠ 1 := by
  simp only [ordOK, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · intro h i hi1 hiK
    have := h (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  · intro h i hi
    exact h (i + 1) (by omega) (by omega)

/-- The candidate list for the auxiliary modulus. -/
