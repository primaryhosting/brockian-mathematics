/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Matrix
open scoped ComplexOrder

/-- Von Neumann entropy of a spectrum `p` (a list of eigenvalues of a density matrix). -/

lemma mpsCoeff_eq_mul {d D k m : ℕ}
    (AL : Fin k → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (AR : Fin m → Fin d → Matrix (Fin D) (Fin D) ℂ) (u v : Fin D → ℂ) :
    mpsCoeff AL AR u v =
      (Matrix.of fun (sL : Fin k → Fin d) (x : Fin D) => (u ᵥ* blockProd AL sL) x) *
      (Matrix.of fun (x : Fin D) (sR : Fin m → Fin d) => (blockProd AR sR *ᵥ v) x) := by
  ext sL sR
  show u ⬝ᵥ ((blockProd AL sL * blockProd AR sR) *ᵥ v) = _
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  rfl

/-- The Schmidt rank of a matrix product state across a cut is at most the bond dimension. -/
