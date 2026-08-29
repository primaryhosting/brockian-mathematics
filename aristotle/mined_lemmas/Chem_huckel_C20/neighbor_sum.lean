import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma neighbor_sum (j k : Fin 20) :
    ∑ u ∈ (cycleGraph 20).neighborFinset j, F u k = F (j - 1) k + F (j + 1) k := by
  have h : (cycleGraph 20).neighborFinset j = {j - 1, j + 1} :=
    cycleGraph_neighborFinset (n := 18) (v := j)
  have hne : (j - 1 : Fin 20) ≠ j + 1 := by revert j; decide
  rw [h, Finset.sum_pair hne]

