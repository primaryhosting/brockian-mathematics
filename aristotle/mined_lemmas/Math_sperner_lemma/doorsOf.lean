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

def doorsOf (c : V → ℕ) (n : ℕ) (σ : Finset V) : Finset (Finset V) :=
  (Finset.powersetCard (n + 1) σ).filter (fun τ => τ.image c = range (n + 1))

/-- Faces of codimension one inside `σ` are exactly the sets `σ.erase x` for `x ∈ σ`. -/
