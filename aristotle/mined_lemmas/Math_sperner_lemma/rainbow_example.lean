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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/

theorem rainbow_example :
    (rainbowCells colour 1 ({{0, 1}, {1, 2}} : Finset (Finset ℕ))).card = 1 := by
  decide

example : Odd (rainbowCells colour 1 ({{0, 1}, {1, 2}} : Finset (Finset ℕ))).card :=
  sperner_lemma carrier colour colour_mem_carrier 1 _ isTri_example

/-! A two-dimensional instance: the triangle `{0,1,2}` subdivided by its barycentre `3` into the
three cells `{0,1,3}`, `{0,2,3}`, `{1,2,3}`, coloured by `c i = i` for `i < 3` and `c 3 = 0`. -/

/-- Carrier faces of the four vertices of the barycentrically subdivided triangle. -/
