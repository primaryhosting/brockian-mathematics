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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma adjMatrix_eq : ((SimpleGraph.cycleGraph 12).adjMatrix ℂ) = C12adj := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  show (if (SimpleGraph.cycleGraph 12).Adj i j then (1 : ℂ) else 0) = _
  congr 1
  simp only [eq_iff_iff, SimpleGraph.cycleGraph_adj]
  revert i j
  decide

/-- **Hückel theory for C₁₂.** A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₁₂` if and only if `μ = 2 cos(2πk/12)` for some `k ∈ {0,…,11}`. -/
