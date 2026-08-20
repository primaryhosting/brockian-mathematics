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

set_option grind.warning false

namespace Chem

open Polynomial

/-- A primitive 8-th root of unity. -/

theorem w8_neg (a : Fin 8) : w8 (-a) = (w8 a)⁻¹ := by
  have h : w8 a * w8 (-a) = 1 := by rw [← w8_add]; simp [w8_zero]
  field_simp [w8_ne_zero a] at h ⊢
  linear_combination h

