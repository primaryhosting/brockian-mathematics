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

lemma mulVec_eigen_neg_one : C6adj.mulVec ![1,-1,0,1,-1,0] = (-1 : ℂ) • ![1,-1,0,1,-1,0] := by
  ext i
  fin_cases i <;> simp [C6adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

