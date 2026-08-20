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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

/-- A primitive sixth root of unity. -/

lemma C6adj_mul_fourierMat :
    C6adj * fourierMat = fourierMat * Matrix.diagonal huckelEigenvalue := by
  ext x k
  rw [Matrix.mul_diagonal]
  have hmul : (C6adj * fourierMat) x k = C6adj.mulVec (fun y => ee (k * y)) x := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, fourierMat]
  rw [hmul, congrFun (C6adj_mulVec_fourier k) x]
  simp [fourierMat, mul_comm]

/-- **Hückel theory for benzene (C₆).** The spectrum of the adjacency matrix of the
cycle graph `C₆` is exactly the set of numbers `2 cos (2πk/6)`, `k = 0, …, 5`. -/
