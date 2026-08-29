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


theorem emb_pone (n r : ℕ) (hr : 0 < r) : emb n r (pone n r) = 1 := by
  rw [emb, pone]
  rw [Finset.sum_eq_single 0]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]
    simp
  · intro b hb hb0
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Finset.mem_range.1 hb)]
    simp [hb0]
  · intro h
    exact absurd (Finset.mem_range.2 hr) h

