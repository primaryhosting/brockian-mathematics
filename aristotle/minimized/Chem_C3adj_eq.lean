/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
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

/-- The Hückel (adjacency) matrix of the cycle graph `C₃`: the π-system connectivity
matrix of a three-membered carbon ring, in units where the Coulomb integral is `α = 0`
and the resonance integral is `β = 1`. -/

noncomputable def C3adj : Matrix (Fin 3) (Fin 3) ℝ :=
  (SimpleGraph.cycleGraph 3).adjMatrix ℝ

/-- Explicit entries of the `C₃` adjacency matrix. -/

lemma C3adj_eq : C3adj = Matrix.of ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C3adj, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph] <;> decide

/-- The Hückel level `2 cos(2πk/3)` for `k = 0` equals `2`. -/
