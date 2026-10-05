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


theorem linProd_injOn (p N : ℕ) [Fact p.Prime] (hN : N ≤ p) :
    ∀ T ⊆ Finset.range N, ∀ T' ⊆ Finset.range N, linProd p T = linProd p T' → T = T' := by
  classical
  have key : ∀ (T : Finset ℕ), T ⊆ Finset.range N → ∀ a < N,
      ((linProd p T).eval (-(a : ZMod p)) = 0 ↔ a ∈ T) := by
    intro T hT a ha
    rw [linProd_eval]
    constructor
    · intro h
      obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.1 h
      have hbN : b < N := Finset.mem_range.1 (hT hb)
      have : ((b : ZMod p)) = ((a : ZMod p)) := by
        have : (-(a : ZMod p)) + (b : ZMod p) = 0 := hb0
        linear_combination this
      have hab : b = a := by
        have h1 : (b : ZMod p).val = b := ZMod.val_cast_of_lt (by omega)
        have h2 : (a : ZMod p).val = a := ZMod.val_cast_of_lt (by omega)
        rw [← h1, ← h2, this]
      rwa [hab] at hb
    · intro h
      refine Finset.prod_eq_zero h ?_
      ring
  intro T hT T' hT' heq
  ext a
  by_cases ha : a < N
  · rw [← key T hT a ha, ← key T' hT' a ha, heq]
  · constructor
    · intro h; exact absurd (Finset.mem_range.1 (hT h)) ha
    · intro h; exact absurd (Finset.mem_range.1 (hT' h)) ha

/-! ## The main criterion -/

