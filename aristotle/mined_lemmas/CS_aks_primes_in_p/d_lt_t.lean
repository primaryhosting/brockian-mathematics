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


theorem d_lt_t {B t : ℕ} (ht : 100 * B ^ 2 < t) :
    2 * (Nat.sqrt t + 1) * B < t := by
  have h1 : 10 * B ≤ Nat.sqrt t := sqrt_ge_of_lt ht
  have h2 : Nat.sqrt t * Nat.sqrt t ≤ t := by
    have := Nat.sqrt_le' t; nlinarith
  have h3 : Nat.sqrt t ≤ t := Nat.sqrt_le_self t
  have hkey : 10 * B * Nat.sqrt t ≤ Nat.sqrt t * Nat.sqrt t :=
    Nat.mul_le_mul_right _ h1
  have ht0 : 0 < t := by nlinarith
  nlinarith

