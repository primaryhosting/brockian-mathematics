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

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

theorem huckel_C12_eigenvector (k : ZMod 12) :
    C12.mulVec (fun j => ee (j * k))
      = (2 * Real.cos (2 * Real.pi * k.val / 12) : ℂ) • fun j => ee (j * k) := by
  funext i
  have h := congrFun (congrFun C12_mul_F i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simpa [Matrix.mulVec, dotProduct, F, lam, mul_comm] using h

end Chem

