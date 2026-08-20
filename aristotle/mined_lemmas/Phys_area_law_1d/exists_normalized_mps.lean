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

lemma exists_normalized_mps :
    ∑ sL : Fin 1 → Fin 2, ∑ sR : Fin 1 → Fin 2,
      ‖mpsCoeff (d := 2) (D := 1) (k := 1) (m := 1)
        (fun _ s => if s = 0 then 1 else 0) (fun _ s => if s = 0 then 1 else 0)
        (fun _ => 1) (fun _ => 1) sL sR‖ ^ 2 = 1 := by
  rw [show (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} from by decide]
  simp [mpsCoeff, blockProd, Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Phys

