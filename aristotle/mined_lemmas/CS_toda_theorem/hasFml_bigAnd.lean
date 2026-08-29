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


theorem hasFml_bigAnd {Q : (Assign → Bool) → Prop} {s : ℕ} :
    ∀ (l : List (Assign → Bool)), (∀ f ∈ l, HasFml Q s f) →
      HasFml Q (l.length * (s + 1) + 1) (bigAnd l)
  | [], _ => by simpa [bigAnd] using HasFml.const (Q := Q) true
  | f :: fs, hl => by
      have hf : HasFml Q s f := hl f (by simp)
      have hfs : HasFml Q (fs.length * (s + 1) + 1) (bigAnd fs) :=
        hasFml_bigAnd fs (fun g hg => hl g (by simp [hg]))
      have := HasFml.and hf hfs
      refine HasFml.mono (this.congr' ?_) ?_
      · intro a; rfl
      · simp [List.length_cons]; ring_nf; omega

/-- The witness block of length `len` starting at position `n + off` is all-zero. -/
