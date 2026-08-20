import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/

theorem purification_exists {rho : Matrix n n ℂ} (h : IsMixedState rho) :
    (∃ psi : n × n → ℂ, IsPurification rho psi ∧ ∑ a : n × n, ‖psi a‖ ^ 2 = 1) ∧
      (∀ (m₁ m₂ : Type) [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]
        (psi₁ : n × m₁ → ℂ) (psi₂ : n × m₂ → ℂ), IsPurification rho psi₁ →
        IsPurification rho psi₂ → Fintype.card m₁ ≤ Fintype.card m₂ →
        ∃ V : Matrix m₂ m₁ ℂ, Vᴴ * V = 1 ∧ psi₂ = ancillaAction V psi₁) := by
  constructor
  · obtain ⟨A, hA, hnorm⟩ := exists_factor_of_isMixedState h
    refine ⟨fun p => A p.1 p.2, ?_, hnorm⟩
    rw [isPurification_iff]
    exact hA
  · intro m₁ m₂ _ _ _ _ psi₁ psi₂ h₁ h₂ hcard
    rw [isPurification_iff] at h₁ h₂
    obtain ⟨W, hW, hBW⟩ :=
      exists_isometry_of_mul_conjTranspose_eq (toMat psi₁) (toMat psi₂) (by rw [h₁, h₂]) hcard
    refine ⟨W.map star, ?_, ?_⟩
    · have key : (W.map star)ᴴ * (W.map star) = (Wᴴ * W)ᵀ := by
        ext b b'
        simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, mul_comm]
      rw [key, hW, Matrix.transpose_one]
    · funext p
      have hp := congrFun (congrFun hBW p.1) p.2
      simpa [ancillaAction, Matrix.mul_apply, Matrix.map_apply, mul_comm] using hp

end Main

section Sanity

/-- The maximally mixed state of a qubit is indeed a mixed state. -/
example : IsMixedState (Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℂ))) := by
  constructor
  · exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by norm_num [Complex.le_def])
  · simp [Matrix.trace_diagonal]

/-- The Bell state is a purification of the maximally mixed state of a qubit. -/
example : IsPurification (Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℂ)))
    (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0) := by
  rw [isPurification_iff]
  ext i j
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;>
    simp [toMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ext_iff] <;>
    field_simp <;> nlinarith [h2, Real.sqrt_nonneg 2]

end Sanity

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

