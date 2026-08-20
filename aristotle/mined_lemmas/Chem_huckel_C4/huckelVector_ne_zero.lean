/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
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

namespace Chem

open Polynomial

/-- The Hückel (adjacency) matrix of the carbon skeleton of cyclobutadiene `C₄`,
i.e. the adjacency matrix of the cycle graph `C₄`, with coefficients in `R`. -/

theorem huckelVector_ne_zero (k : Fin 4) : huckelVector k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [huckelVector_eq] at h0
  simp at h0

/-- Each Hückel mode is an eigenvector of the `C₄` adjacency matrix with eigenvalue
`2 cos (2πk/4)`. -/
