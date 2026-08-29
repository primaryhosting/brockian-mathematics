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

theorem isTri_example2 :
    IsTri carrier2 2 ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Finset ℕ)) :=
  ⟨by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide, ⟨0, by decide, by decide⟩⟩⟩

