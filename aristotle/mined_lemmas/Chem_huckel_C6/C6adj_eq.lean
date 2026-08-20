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

namespace Chem

open Polynomial

/-- The Hückel matrix of benzene (in units where the Coulomb integral `α` is `0` and the
resonance integral `β` is `1`): the adjacency matrix of the cycle graph `C₆`. -/

theorem C6adj_eq :
    C6adj = !![0, 1, 0, 0, 0, 1;
                1, 0, 1, 0, 0, 0;
                0, 1, 0, 1, 0, 0;
                0, 0, 1, 0, 1, 0;
                0, 0, 0, 1, 0, 1;
                1, 0, 0, 0, 1, 0] := by
  unfold C6adj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.adjMatrix_apply, Matrix.cons_val] <;> decide

/-- The characteristic polynomial of the adjacency matrix of `C₆`. -/
