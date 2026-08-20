import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realised concretely as the Hilbert space
of functions `Fin 2 × Fin 2 → ℂ` with the standard inner product. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Unnormalised coefficients of the four Bell states in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`. -/

theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ ∧
      ∃ b : OrthonormalBasis (Fin 4) ℂ TwoQubit, ⇑b = bell :=
  ⟨bell_orthonormal_family, by
    have h := (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family
      card_eq_finrank).span_eq
    rwa [coe_basisOfOrthonormalOfCardEqFinrank] at h,
    bellBasis, coe_bellBasis⟩

end QC

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

