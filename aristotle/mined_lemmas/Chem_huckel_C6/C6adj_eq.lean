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

namespace Chem

open Polynomial Matrix

/-- The Hückel (adjacency) matrix of the cycle graph `C₆` (the benzene ring), over `ℂ`. -/

lemma C6adj_eq :
    C6adj = !![0,1,0,0,0,1;
               1,0,1,0,0,0;
               0,1,0,1,0,0;
               0,0,1,0,1,0;
               0,0,0,1,0,1;
               1,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj] <;> decide

/-- Matrix whose columns are eigenvectors of the `C₆` adjacency matrix. -/
