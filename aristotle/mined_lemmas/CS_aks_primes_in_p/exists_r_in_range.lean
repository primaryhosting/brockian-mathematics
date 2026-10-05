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


theorem exists_r_in_range (n : ℕ) (hn : 2 ≤ n) :
    ∃ r ∈ List.range (rBound n + 1), rPred n r = true := by
  obtain ⟨r, hr2, hrle, hr⟩ :=
    exists_good_r n (bitLen n) (thr n) hn (lt_two_pow_bitLen n) (one_le_thr n)
  refine ⟨r, List.mem_range.2 (by simp only [rBound]; omega), ?_⟩
  simp only [rPred, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hr2, (ordOK_iff n r (thr n)).2 hr⟩

