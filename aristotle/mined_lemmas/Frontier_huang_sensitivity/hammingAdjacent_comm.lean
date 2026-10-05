/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` commands to precede every other command, including module
-- docstrings, so the header above is repeated as a module docstring after the imports.)

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

set_option grind.warning false

namespace Frontier

/-- Two vertices of the Boolean hypercube `{0,1}^n = (Fin n → Bool)` are adjacent when they
differ in exactly one coordinate. -/

lemma hammingAdjacent_comm {n : ℕ} (p q : Fin n → Bool) :
    HammingAdjacent p q ↔ HammingAdjacent q p := by
  simp only [HammingAdjacent, ne_comm]

/-- The set of neighbours of `q` inside `H`, as used to measure the degree of `q` in the
subgraph of the hypercube induced by `H`. -/
