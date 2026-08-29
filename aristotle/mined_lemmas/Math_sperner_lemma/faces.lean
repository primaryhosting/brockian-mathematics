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

def faces (K : Finset (Finset V)) (k : ℕ) : Finset (Finset V) :=
  K.biUnion (fun σ => Finset.powersetCard k σ)

/-- The sub-complex of `K` consisting of the boundary faces lying in the facet
opposite to the vertex `n + 1`: the `(n+1)`-element faces contained in a unique cell
and all of whose vertices have carrier avoiding the index `n + 1`. -/
