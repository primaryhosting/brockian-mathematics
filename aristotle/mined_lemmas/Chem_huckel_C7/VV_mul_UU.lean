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

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of cycloheptatrienyl,
with `α = 0`, `β = 1`), as a real `7 × 7` matrix. -/

lemma VV_mul_UU : VV * UU = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 7, VV k j * UU j l = (7 : ℂ)⁻¹ * ee (j * (l - k)) := by
    intro j
    simp only [UU, VV, Matrix.of_apply]
    rw [fin7_mul_sub_right j k l, ee_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum, sum_ee]
  by_cases h : k = l
  · subst h
    simp
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm h)), Matrix.one_apply_ne h, mul_zero]

