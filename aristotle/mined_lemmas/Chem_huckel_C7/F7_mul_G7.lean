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

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `±1` mod `7`. -/

private lemma F7_mul_G7 : F7 * G7 = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [F7, G7, Matrix.of_apply]
  have key : ∀ k : ZMod 7, ZMod.stdAddChar (i * k) * ((7 : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j)))
      = (7 : ℂ)⁻¹ * ZMod.stdAddChar ((i - j) * k) := by
    intro k
    rw [← mul_assoc, mul_comm (ZMod.stdAddChar (i * k)) ((7 : ℂ)⁻¹), mul_assoc,
      ← AddChar.map_add_eq_mul]
    ring_nf
  simp only [key, ← Finset.mul_sum, stdAddChar_sum, sub_eq_zero]
  by_cases h : i = j
  · rw [h]
    simp [Matrix.one_apply_eq]
  · simp [h, Matrix.one_apply_ne h]

