/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

theorem huckel_C20_eigenvector (k : ZMod 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) *ᵥ (fun j : ZMod 20 => e (j * k))
      = (2 * Real.cos (2 * Real.pi * k.val / 20) : ℂ) • (fun j : ZMod 20 => e (j * k)) := by
  rw [← adjC20_eq_cycleGraph]
  funext i
  have h := congrFun (congrFun adj_mul_dft i) k
  rw [diagC20, Matrix.mul_diagonal, Matrix.mul_apply] at h
  simp only [dftMat, Matrix.of_apply] at h
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

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

