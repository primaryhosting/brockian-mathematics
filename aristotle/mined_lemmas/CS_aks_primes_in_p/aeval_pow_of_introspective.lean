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


theorem aeval_pow_of_introspective {p r m : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [Algebra (ZMod p) K] {x : K} (hx : x ^ r = 1) {f : (ZMod p)[X]}
    (h : Introspective r m f) : (aeval x f) ^ m = aeval (x ^ m) f := by
  obtain ⟨q, hq⟩ := h
  have := congrArg (fun g : (ZMod p)[X] => aeval x g) hq
  simp only [map_sub, map_pow, aeval_comp, aeval_X, map_one, hx, sub_self, zero_mul,
    map_mul] at this
  exact sub_eq_zero.mp this

/-! ## Products of linear polynomials -/

/-- The polynomial `∏_{a ∈ T} (X + a)` over `ZMod p`. -/
