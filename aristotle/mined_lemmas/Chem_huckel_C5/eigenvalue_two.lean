/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
with `α = 0`, `β = 1`), with vertices `0,1,2,3,4` arranged in a pentagon. -/

lemma eigenvalue_two : C5adj *ᵥ (fun _ => (1:ℝ)) = (2:ℝ) • (fun _ => (1:ℝ)) := by
  ext i
  fin_cases i <;>
    norm_num [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Chem

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

