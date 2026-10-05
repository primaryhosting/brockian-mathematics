/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- The standard additive character `ZMod 14 → ℂ`, `j ↦ exp (2πI j / 14)`. -/

lemma U14_mul_V14 : U14 * V14 = 1 := by
  ext j l
  have hsum : ∑ x : ZMod 14, ee (x * (j - l))
      = ((if (j - l : ZMod 14) = 0 then (Fintype.card (ZMod 14)) else 0 : ℕ) : ℂ) :=
    AddChar.sum_mulShift (ψ := ee) (j - l) (ZMod.isPrimitive_stdAddChar 14)
  have hcard : Fintype.card (ZMod 14) = 14 := by simp
  rw [hcard] at hsum
  simp only [Matrix.mul_apply, U14, V14]
  have hterm : ∀ x : ZMod 14, ee (j * x) * ((14 : ℂ)⁻¹ * ee (-(x * l)))
      = (14 : ℂ)⁻¹ * ee (x * (j - l)) := by
    intro x
    have : x * (j - l) = j * x + -(x * l) := by ring
    rw [this, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum, hsum]
  by_cases h : j = l
  · subst h
    simp
  · have h' : (j - l : ZMod 14) ≠ 0 := sub_ne_zero_of_ne h
    simp [h', h]

