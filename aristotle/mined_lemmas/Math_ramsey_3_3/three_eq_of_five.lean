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

namespace Math

/-- `MonoTriangle c i j k` says that the three distinct vertices `i, j, k` span a
triangle all of whose edges get the same colour under the edge-colouring `c`. -/
abbrev MonoTriangle {n : ℕ} (c : Fin n → Fin n → Bool) (i j k : Fin n) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ c i j = c j k ∧ c i j = c i k

/-- Among five booleans, three of them (at distinct, increasing indices) are equal. -/

lemma three_eq_of_five (b : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i < j ∧ j < k ∧ b i = b j ∧ b j = b k := by
  revert b; decide

/-- Every 2-colouring of the edges of `K₆` contains a monochromatic triangle.
(No symmetry assumption on `c` is needed here: the triangle produced only uses
edges read in one fixed orientation.) -/
