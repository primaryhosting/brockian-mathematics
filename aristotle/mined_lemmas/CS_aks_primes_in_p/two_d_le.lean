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


theorem two_d_le {B t r : ℕ} (ht : 100 * B ^ 2 < t) (htr : t ≤ r) :
    2 * (2 * (Nat.sqrt t + 1) * B) ≤ r := by
  have h1 : 10 * B ≤ Nat.sqrt r := sqrt_ge_of_lt (lt_of_lt_of_le ht htr)
  have h2 : Nat.sqrt r * Nat.sqrt r ≤ r := by
    have := Nat.sqrt_le' r; nlinarith
  have h3 : Nat.sqrt t ≤ Nat.sqrt r := Nat.sqrt_le_sqrt htr
  have h4 : Nat.sqrt r ≤ r := Nat.sqrt_le_self r
  have hkey : 10 * B * Nat.sqrt r ≤ Nat.sqrt r * Nat.sqrt r :=
    Nat.mul_le_mul_right _ h1
  have hkey2 : Nat.sqrt t * B ≤ Nat.sqrt r * B := Nat.mul_le_mul_right _ h3
  nlinarith

