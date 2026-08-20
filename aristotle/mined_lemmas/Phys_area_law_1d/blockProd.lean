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

noncomputable def blockProd {L d D : ℕ} (A : Fin L → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (s : Fin L → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i => A i (s i)).prod

/-- Coefficient matrix, across the cut, of a matrix product state on a 1D chain consisting of a
left block of `k` sites and a right block of `m` sites, each of local dimension `d`, with bond
dimension `D` and boundary vectors `u`, `v`. -/
