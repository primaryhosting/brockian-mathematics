/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- A 2-colouring `C` of the edges of the complete graph on `Fin n` has a monochromatic
triangle if there are three distinct vertices all of whose connecting edges receive the
same colour. -/

lemma pentagon_no_mono : ¬ HasMonoTriangle pentagon := by
  unfold HasMonoTriangle
  decide

/-- Every 2-colouring of the edges of `K₆` contains a monochromatic triangle.
(The symmetry hypothesis `hC`, which expresses that `C` really is an edge-colouring,
turns out not to be needed for this direction.) -/
