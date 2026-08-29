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


theorem cong_X_pow_mod {R : Type*} [CommRing R] (r a : ℕ) (hr : 0 < r) :
    Cong r (X ^ a : R[X]) (X ^ (a % r)) := by
  refine ⟨X ^ (a % r) * (∑ i ∈ Finset.range (a / r), (X ^ r) ^ i), ?_⟩
  have hgeom : ((X : R[X]) ^ r - 1) * (∑ i ∈ Finset.range (a / r), (X ^ r) ^ i)
      = (X ^ r) ^ (a / r) - 1 := by
    rw [mul_comm]
    exact geom_sum_mul _ _
  calc (X : R[X]) ^ a - X ^ (a % r)
      = X ^ (a % r) * ((X ^ r) ^ (a / r) - 1) := by
        rw [mul_sub, mul_one, ← pow_mul, ← pow_add]
        congr 2
        exact (Nat.mod_add_div a r).symm
    _ = (X ^ r - 1) * (X ^ (a % r) * (∑ i ∈ Finset.range (a / r), (X ^ r) ^ i)) := by
        rw [← hgeom]; ring

/-! ## Coefficient lists -/

/-- The polynomial represented by a coefficient list of length `r`. -/
