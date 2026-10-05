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


theorem findR_spec (n : ℕ) (hn : 2 ≤ n) : rPred n (findR n) = true ∧ findR n ≤ rBound n := by
  rcases h : (List.range (rBound n + 1)).find? (fun r => rPred n r) with _ | r
  · exfalso
    rw [List.find?_eq_none] at h
    obtain ⟨r, hr, hr'⟩ := exists_r_in_range n hn
    exact (h r hr) hr'
  · have h1 : rPred n r = true := List.find?_some h
    have h2 : r ∈ List.range (rBound n + 1) := List.mem_of_find?_eq_some h
    refine ⟨?_, ?_⟩ <;> rw [findR, h] <;> simp only [Option.getD_some]
    · exact h1
    · exact Nat.lt_succ_iff.1 (List.mem_range.1 h2)

