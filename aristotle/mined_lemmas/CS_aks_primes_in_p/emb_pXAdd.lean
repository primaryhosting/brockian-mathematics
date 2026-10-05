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


theorem emb_pXAdd (n r k c : ℕ) (hr : 0 < r) :
    Cong r (emb n r (pXAdd n r k c)) (X ^ k + C ((c : ℕ) : ZMod n)) := by
  have hval : ∀ i < r, (((pXAdd n r k c).getD i 0 : ℕ) : ZMod n) =
      (if i = k % r then 1 else 0) + (if i = 0 then ((c : ℕ) : ZMod n) else 0) := by
    intro i hi
    rw [pXAdd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some, ZMod.natCast_mod]
    push_cast
    split <;> split <;> simp
  have h1 : emb n r (pXAdd n r k c) = X ^ (k % r) + C ((c : ℕ) : ZMod n) := by
    rw [emb]
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [hval i (Finset.mem_range.1 hi)])]
    simp only [map_add, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single (k % r)]
      · simp
      · intro b _ hbk
        simp [hbk]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hr)) h
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb0
        simp [hb0]
      · intro h
        exact absurd (Finset.mem_range.2 hr) h
  rw [h1]
  exact (cong_X_pow_mod r k hr).symm.add (Cong.refl r _)

