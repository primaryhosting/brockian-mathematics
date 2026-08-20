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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma sum_ee_mul (m : ZMod 12) : ∑ k : ZMod 12, ee (k * m) = if m = 0 then 12 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero, ZMod.card]
  · simp only [hm, if_false]
    set S : ℂ := ∑ k : ZMod 12, ee (k * m) with hS
    have hstep : S * ee m = S := by
      have h1 : S * ee m = ∑ k : ZMod 12, ee ((k + 1) * m) := by
        rw [hS, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (k + 1) * m = k * m + m by ring, ee_add]
      rw [h1]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod 12)) (fun k => ee (k * m))
    have : S * (ee m - 1) = 0 := by rw [mul_sub, hstep, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by linear_combination h) (ee_ne_one hm)

