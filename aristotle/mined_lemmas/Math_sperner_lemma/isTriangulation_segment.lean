/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

theorem isTriangulation_segment :
    IsTriangulation (V := ℕ) 1 {0, 1} {{0, 1}, {1, 2}} segmentCarrier := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro a ha
  fin_cases ha <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Existence form of Sperner's lemma**: a Sperner colouring of a triangulated simplex
admits at least one rainbow cell. -/
