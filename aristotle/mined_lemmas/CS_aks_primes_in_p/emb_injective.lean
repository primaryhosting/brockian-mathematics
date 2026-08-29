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


theorem emb_injective (n r : ℕ) [Fact n.Prime] (hr : 0 < r) {f g : List ℕ}
    (hf : f.length = r) (hg : g.length = r)
    (hfb : ∀ k < r, f.getD k 0 < n) (hgb : ∀ k < r, g.getD k 0 < n)
    (h : Cong r (emb n r f) (emb n r g)) : f = g := by
  have hn : 1 < n := (Fact.out (p := n.Prime)).one_lt
  haveI : NeZero n := ⟨by omega⟩
  have hdegdvd : (X ^ r - 1 : (ZMod n)[X]).degree = (r : ℕ) := by
    have : (X ^ r - 1 : (ZMod n)[X]) = X ^ r - C 1 := by simp
    rw [this, Polynomial.degree_X_pow_sub_C hr]
  have hzero : emb n r f - emb n r g = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h ?_
    rw [hdegdvd]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (degree_emb_lt n r f) (degree_emb_lt n r g))
  have heq : emb n r f = emb n r g := by
    have := sub_eq_zero.1 hzero
    exact this
  refine List.ext_getElem (by omega) ?_
  intro k h1 h2
  have hk : k < r := by omega
  have hcoeff : ((f.getD k 0 : ℕ) : ZMod n) = ((g.getD k 0 : ℕ) : ZMod n) := by
    rw [← emb_getD n r f k hk, ← emb_getD n r g k hk, heq]
  have hval : f.getD k 0 = g.getD k 0 := by
    have h3 : ((f.getD k 0 : ℕ) : ZMod n).val = ((g.getD k 0 : ℕ) : ZMod n).val := by
      rw [hcoeff]
    rwa [ZMod.val_cast_of_lt (hfb k hk), ZMod.val_cast_of_lt (hgb k hk)] at h3
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hval

end AKS

import RequestProject.AKS.Core
import RequestProject.AKS.SmallR
import RequestProject.AKS.PolyList

/-!
# The AKS primality test

This file defines the decision procedure `AKS.aksTest : ℕ → Bool` and proves
`AKS.aksTest_iff_prime : aksTest n = true ↔ n.Prime`.

All the searches performed by the test are bounded by explicit polynomials in the bit length
of the input (see `AKS.findR_le`).
-/

namespace AKS

open Polynomial Finset

/-- Bit length of `n`. -/
