import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

theorem exists_quantumMeasure_not_density_dim_two :
    ∃ mu : Matrix (Fin 2) (Fin 2) ℂ → ℝ, IsQuantumMeasure mu ∧
      ¬ ∃ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityOperator rho ∧
        ∀ P : Matrix (Fin 2) (Fin 2) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace :=
  ⟨qubitMeasure, isQuantumMeasure_qubitMeasure, not_exists_density_for_qubitMeasure⟩

end Frontier

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

