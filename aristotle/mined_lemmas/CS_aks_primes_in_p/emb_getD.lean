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


theorem emb_getD (n r : ℕ) (l : List ℕ) (k : ℕ) (hk : k < r) :
    (emb n r l).coeff k = ((l.getD k 0 : ℕ) : ZMod n) := by
  rw [emb, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hbk]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h

