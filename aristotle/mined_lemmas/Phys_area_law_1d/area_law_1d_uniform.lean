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

theorem area_law_1d_uniform {d D : ℕ} (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (u v : Fin D → ℂ) (k m : ℕ)
    (hnorm : ∑ sL : Fin k → Fin d, ∑ sR : Fin m → Fin d,
        ‖mpsCoeff (fun i : Fin k => A i) (fun j : Fin m => A (k + j)) u v sL sR‖ ^ 2 = 1) :
    entanglementEntropy (mpsCoeff (fun i : Fin k => A i) (fun j : Fin m => A (k + j)) u v)
      ≤ Real.log D :=
  area_law_1d _ _ u v hnorm

/-- The normalization hypothesis of `Phys.area_law_1d` is satisfiable: an explicit normalized
matrix product state (here the product state on two qubits with bond dimension one).  This shows
the area law above is not vacuous. -/
