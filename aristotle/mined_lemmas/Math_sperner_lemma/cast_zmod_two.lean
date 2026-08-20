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

/-!
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/

lemma cast_zmod_two (m : ℕ) : (m : ZMod 2) = if Odd m then 1 else 0 := by
  have h2 : ((m % 2 : ℕ) : ZMod 2) = (m : ZMod 2) := ZMod.natCast_mod m 2
  rw [← h2]
  rcases Nat.even_or_odd m with h | h
  · rw [Nat.even_iff] at h; rw [h]; simp [Nat.odd_iff, h]
  · rw [Nat.odd_iff] at h; rw [h]; simp [Nat.odd_iff, h]

/-- The faces of size `n+1` of a cell `σ` of size `n+2` are exactly the sets `σ.erase v`. -/
