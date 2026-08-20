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

@[simp] theorem card_words (n : ℕ) : (words n).card = 2 ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
      have hdisj :
          Disjoint ((words n).image (List.cons false)) ((words n).image (List.cons true)) := by
        rw [Finset.disjoint_left]
        rintro l hl hl'
        simp only [Finset.mem_image] at hl hl'
        obtain ⟨t, _, rfl⟩ := hl
        obtain ⟨t', _, h⟩ := hl'
        simp at h
      have h1 : ((words n).image (List.cons false)).card = (words n).card :=
        Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)
      have h2 : ((words n).image (List.cons true)).card = (words n).card :=
        Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)
      rw [words, Finset.card_union_of_disjoint hdisj, h1, h2, ih]
      ring

/-- The set of length-`N` extensions of a word `w`. -/
