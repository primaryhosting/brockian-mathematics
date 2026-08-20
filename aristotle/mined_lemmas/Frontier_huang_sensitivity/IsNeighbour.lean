/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` lines to precede every command, including a
module docstring `/-! ... -/`, so this header is a plain comment and the
module docstring below repeats it after the imports.)
-/

import Mathlib
import Archive.Sensitivity

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Two points of the discrete hypercube `Fin n → Bool` are neighbours when they
differ in exactly one coordinate. -/

def IsNeighbour {n : ℕ} (p q : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i : Fin n => p i ≠ q i).card = 1

/-- Being a neighbour in the hypercube is the same as being adjacent in the sense
of the hypercube graph (`∃! i, p i ≠ q i`). -/
