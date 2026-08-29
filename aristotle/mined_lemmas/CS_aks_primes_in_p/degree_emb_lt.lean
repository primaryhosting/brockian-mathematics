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


theorem degree_emb_lt (n r : ℕ) (l : List ℕ) : (emb n r l).degree < (r : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  have hm' : r ≤ m := by exact_mod_cast hm
  rw [emb, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < r := Finset.mem_range.1 hi
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (m = i)), mul_zero]

