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

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma sum_xi (d : ZMod 12) : ∑ j : ZMod 12, xi (j * d) = if d = 0 then 12 else 0 := by
  have hstep : ∀ j : ZMod 12, xi (j * d) = xi d ^ j.val := fun j => xi_mul j d
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  have hrange : ∑ j : ZMod 12, xi d ^ j.val = ∑ n ∈ Finset.range 12, xi d ^ n :=
    Fin.sum_univ_eq_sum_range (fun n => xi d ^ n) 12
  rw [hrange]
  by_cases hd : d = 0
  · subst hd; simp [xi_zero]
  · rw [if_neg hd]
    have h1 : xi d ≠ 1 := fun h => hd ((xi_eq_one_iff d).mp h)
    rw [geom_sum_eq h1, xi_pow_twelve, sub_self, zero_div]

