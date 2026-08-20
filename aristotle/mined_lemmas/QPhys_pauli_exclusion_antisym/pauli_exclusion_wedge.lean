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

namespace QPhys

open TensorProduct

variable {𝕜 H : Type*} [Field 𝕜] [AddCommGroup H] [Module 𝕜 H]

/-- The antisymmetrized (fermionic) two-particle state built from two single-particle
states `u` and `v`, living in `H ⊗ H`:  `antisymState u v = u ⊗ v - v ⊗ u`. -/

theorem pauli_exclusion_wedge (u : H) :
    (ExteriorAlgebra.ι 𝕜 u) * (ExteriorAlgebra.ι 𝕜 u) = 0 :=
  ExteriorAlgebra.ι_sq_zero u

/-- Pauli exclusion for Slater determinants of wavefunctions on a set of modes `ι`:
the two-particle wavefunction `Ψ i j = f i * g j - f j * g i` vanishes identically
when the two single-particle wavefunctions coincide. -/
