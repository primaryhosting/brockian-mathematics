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

import Mathlib
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma natCast_pow_sub_one [CharP F q] (hq : q.Prime) (m : ℕ) :
    ((m : F)) ^ (q - 1) = if q ∣ m then 0 else 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases h : q ∣ m
  · have h0 : (m : F) = 0 := by rwa [CharP.cast_eq_zero_iff F q]
    rw [h0, if_pos h, zero_pow]
    have := hq.two_le
    omega
  · rw [if_neg h]
    have hz : ((m : ZMod q)) ≠ 0 := fun hc => h ((CharP.cast_eq_zero_iff (ZMod q) q m).1 hc)
    have hone := ZMod.pow_card_sub_one_eq_one hz
    have hmap : ((m : F)) = (ZMod.castHom (dvd_refl q) F) (m : ZMod q) := by simp
    rw [hmap, ← map_pow, hone, map_one]

/-- The approximating polynomial for an `OR` gate given a choice of random subsets `ω`. -/
