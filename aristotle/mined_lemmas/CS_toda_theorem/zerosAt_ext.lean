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
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem zerosAt_ext {n off len W : ℕ} (h : off + len ≤ W) (x : Assign) (y : Fin W → Bool) :
    zerosAt n off len (ext n W x y) = true ↔ ∀ j : Fin len, y ⟨off + j.1, by omega⟩ = false := by
  rw [zerosAt, bigAnd_eq_true]
  constructor
  · intro hh j
    have hj : (fun a : Assign => !a (n + off + j.1)) ∈
        (List.range len).map (fun j => fun a : Assign => !a (n + off + j)) := by
      simp only [List.mem_map, List.mem_range]
      exact ⟨j.1, j.2, rfl⟩
    have := hh _ hj
    have hlt : off + j.1 < W := by omega
    have hval : ext n W x y (n + (off + j.1)) = y ⟨off + j.1, hlt⟩ := ext_ge hlt
    have hidx : n + off + j.1 = n + (off + j.1) := by omega
    rw [hidx, hval] at this
    simpa using this
  · intro hh f hf
    simp only [List.mem_map, List.mem_range] at hf
    obtain ⟨j, hj, rfl⟩ := hf
    have hlt : off + j < W := by omega
    have hval : ext n W x y (n + (off + j)) = y ⟨off + j, hlt⟩ := ext_ge hlt
    have hidx : n + off + j = n + (off + j) := by omega
    simp only [hidx, hval]
    have := hh ⟨j, hj⟩
    simp only at this
    simp [this]

/-! ### Gap data -/

/-- A description of a "gap function": a witness length together with predicates
describing the accepting (`pos`) and rejecting (`neg`) witnesses.  The value is the
number of accepting witnesses minus the number of rejecting ones. -/
structure GapData where
  w : ℕ
  pos : Assign → Bool
  neg : Assign → Bool

namespace GapData

/-- The weight of a single witness. -/
