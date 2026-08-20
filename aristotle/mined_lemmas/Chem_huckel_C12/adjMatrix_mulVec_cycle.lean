/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma adjMatrix_mulVec_cycle (v : Fin 12 → ℂ) (i : Fin 12) :
    ((SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hnb : (SimpleGraph.cycleGraph 12).neighborFinset i = {i - 1, i + 1} := by
    exact SimpleGraph.cycleGraph_neighborFinset (n := 10)
  rw [hnb, Finset.sum_pair (by revert i; decide)]

/-- The discrete Fourier orthogonality relation. -/
