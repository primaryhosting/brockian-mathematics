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


theorem introspective_of_polyOK {n r a : ℕ} (hr : 0 < r) (h : polyOK n r a = true) :
    Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X]) := by
  rw [polyOK, beq_iff_eq] at h
  have h1 : Cong r (emb n r (ppow n r (pXAdd n r 1 a) n))
      (((X : (ZMod n)[X]) + C ((a : ℕ) : ZMod n)) ^ n) := by
    refine (emb_ppow n r hr _ n).trans ?_
    refine Cong.pow ?_ n
    have := emb_pXAdd n r 1 a hr
    simpa using this
  have h2 : Cong r (emb n r (pXAdd n r n a))
      ((X : (ZMod n)[X]) ^ n + C ((a : ℕ) : ZMod n)) := emb_pXAdd n r n a hr
  have := (h1.symm.trans (h ▸ h2))
  rw [Introspective, comp_X_add_C]
  exact this

/-- For prime `n` the list-level test `polyOK` succeeds. -/
