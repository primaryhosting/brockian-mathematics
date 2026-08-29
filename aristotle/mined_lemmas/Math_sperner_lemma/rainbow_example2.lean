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

theorem rainbow_example2 :
    (rainbowCells colour2 2 ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Finset ℕ))).card = 1 := by
  decide

example : Odd (rainbowCells colour2 2 ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Finset ℕ))).card :=
  sperner_lemma carrier2 colour2 colour2_mem_carrier2 2 _ isTri_example2

end Example

end Math

