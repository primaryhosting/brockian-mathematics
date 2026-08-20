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

namespace CS

/-- The finite set of all binary words (lists of booleans) of length `n`. -/

@[simp] theorem mem_words {n : ℕ} {l : List Bool} : l ∈ words n ↔ l.length = n := by
  induction n generalizing l with
  | zero =>
      simp [words, List.length_eq_zero_iff]
  | succ n ih =>
      constructor
      · intro hl
        simp only [words, Finset.mem_union, Finset.mem_image] at hl
        rcases hl with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
          simp [ih.mp ht]
      · intro hl
        match l with
        | [] => simp at hl
        | b :: t =>
            have ht : t.length = n := by simpa using hl
            cases b <;>
              simp only [words, Finset.mem_union, Finset.mem_image] <;>
              [left; right] <;> exact ⟨t, ih.mpr ht, rfl⟩

