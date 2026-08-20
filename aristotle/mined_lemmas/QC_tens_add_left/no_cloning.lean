import Mathlib

/-!
# The no-cloning theorem

We model a single qubit by `Qubit := EuclideanSpace ℂ (Fin 2)` and the two-qubit
space `H ⊗ H` by `TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the tensor
product of vectors given coordinatewise by `Qubit.tens`.

A *unitary* operator on the two-qubit space is a surjective linear isometry, i.e. a
term of type `TwoQubit ≃ₗᵢ[ℂ] TwoQubit`.

The main result `QC.no_cloning` states that for every "blank" vector `blank` and every
unitary `U` there is a state `ψ` (a unit vector) with `U (ψ ⊗ blank) ≠ ψ ⊗ ψ`.
-/

namespace QC

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `Qubit ⊗ Qubit`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `|ψ⟩ ⊗ |φ⟩` of two qubit states. -/

theorem no_cloning (blank : Qubit) :
    ¬ ∃ U : TwoQubit ≃ₗᵢ[ℂ] TwoQubit, ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tens ψ blank) = tens ψ ψ := by
  rintro ⟨U, h⟩
  have h0 := h e0 norm_e0
  have h1 := h e1 norm_e1
  have hp := h plus norm_plus
  -- expand the left-hand side by linearity
  have hlin : U (tens plus blank)
      = ((Real.sqrt 2 : ℂ))⁻¹ • (tens e0 e0 + tens e1 e1) := by
    rw [plus, tens_smul_left, tens_add_left, map_smul, map_add, h0, h1]
  rw [hp] at hlin
  -- compare the coordinate `(0, 1)`
  have hco := congrArg (fun x : TwoQubit => x.ofLp (0, 1)) hlin
  simp only [tens_apply, PiLp.smul_apply, smul_eq_mul] at hco
  rw [plus] at hco
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, e0, e1,
    EuclideanSpace.single_apply] at hco
  norm_num at hco

#print axioms QC.no_cloning

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

