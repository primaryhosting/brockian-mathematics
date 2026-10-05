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

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene with
`α = 0`, `β = 1`), written out explicitly. -/

lemma ne_zero_of_first_ne_zero (v : Fin 6 → ℂ) (h : v 0 ≠ 0) : v ≠ 0 := by
  intro hv
  exact h (by rw [hv]; rfl)

end Eigenvectors

/-- **Hückel theory for benzene (C₆).**  A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₆` if and only if `μ = 2 cos (2πk/6)` for some `k ∈ {0,1,2,3,4,5}`.
(Equivalently, the Hückel π-orbital energies of benzene are `α + 2β cos(2πk/6)`.) -/
