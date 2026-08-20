/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A mixed state on `ℂ^n` is modelled by a density matrix `rho : Matrix n n ℂ`, i.e. a positive
semidefinite matrix of unit trace.  A vector of the composite system `ℂ^n ⊗ ℂ^m` is modelled by
a matrix `M : Matrix n m ℂ` (its matrix of coefficients in the product basis), the squared
Hilbert–Schmidt norm `∑ i j, ‖M i j‖ ^ 2` being its squared norm as a vector, and its partial
trace over the ancilla `ℂ^m` being `M * Mᴴ`.

The main result `QI.purification_exists` states that every mixed state `rho` has a purification
by a unit vector of `ℂ^n ⊗ ℂ^n`, and that any two purifications with the same ancilla differ by
a unitary acting on the ancilla only.
-/

open scoped BigOperators
open scoped ComplexConjugate
open scoped ComplexOrder
open scoped MatrixOrder

namespace QI

open Matrix

/-- A *mixed state* (density matrix) on the finite-dimensional Hilbert space `ℂ^n`:
a positive semidefinite matrix of unit trace. -/

theorem purification_exists {n : Type} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) (h : IsMixedState rho) :
    (∃ M : Matrix n n ℂ, IsPurification rho M ∧ ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1) ∧
      ∀ (m : Type) [Fintype m] [DecidableEq m] (M N : Matrix n m ℂ),
        IsPurification rho M → IsPurification rho N →
          ∃ W : Matrix m m ℂ, W ∈ Matrix.unitaryGroup m ℂ ∧ N = M * W := by
  obtain ⟨hpsd, htr⟩ := h
  constructor
  · -- the positive semidefinite square root of `rho` is a purification
    refine ⟨CFC.sqrt rho, ?_, ?_⟩
    · have h2 : (CFC.sqrt rho).PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
      show CFC.sqrt rho * (CFC.sqrt rho)ᴴ = rho
      rw [h2.isHermitian.eq]
      exact CFC.sqrt_mul_sqrt_self rho hpsd.nonneg
    · have h2 : (CFC.sqrt rho).PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
      have hpur : CFC.sqrt rho * (CFC.sqrt rho)ᴴ = rho := by
        rw [h2.isHermitian.eq]; exact CFC.sqrt_mul_sqrt_self rho hpsd.nonneg
      have := trace_mul_conjTranspose (CFC.sqrt rho)
      rw [hpur, htr] at this
      exact_mod_cast this.symm
  · intro m _ _ M N hM hN
    exact exists_unitary_of_mul_conjTranspose_eq M N (by rw [hM, hN])

/-- Sanity check that the hypothesis of `purification_exists` is satisfiable: the maximally
mixed state of a qubit is a mixed state. -/
example : IsMixedState ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_, by simp [Matrix.trace_smul]⟩
  rw [RCLike.nonneg_iff]
  norm_num

end QI

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

