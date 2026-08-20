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

lemma exists_linearIsometry_comp_eq {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f g : E →ₗ[ℂ] V) (hnorm : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : V →ₗᵢ[ℂ] V, ∀ x, U (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have h0 : ‖g x‖ = 0 := by rw [← hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp h0)
  let L₀ : (E ⧸ LinearMap.ker f) →ₗ[ℂ] V := (LinearMap.ker f).liftQ g hker
  let Lmap : (LinearMap.range f) →ₗ[ℂ] V :=
    L₀ ∘ₗ (f.quotKerEquivRange.symm : LinearMap.range f →ₗ[ℂ] (E ⧸ LinearMap.ker f))
  have hLmap : ∀ x : E, Lmap ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    show L₀ (f.quotKerEquivRange.symm ⟨f x, ⟨x, rfl⟩⟩) = g x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp [L₀]
  let L : (LinearMap.range f) →ₗᵢ[ℂ] V := ⟨Lmap, by
    intro s
    obtain ⟨x, hx⟩ := s.2
    have hs : s = ⟨f x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
    rw [hs, hLmap x]
    show ‖g x‖ = ‖(⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range f)‖
    rw [← hnorm x]
    rfl⟩
  refine ⟨L.extend, fun x => ?_⟩
  have h1 := L.extend_apply ⟨f x, ⟨x, rfl⟩⟩
  have h2 : (L ⟨f x, ⟨x, rfl⟩⟩ : V) = g x := hLmap x
  rw [h2] at h1
  exact h1

/-- The matrix of a linear isometry of `ℂ^m` in the standard (orthonormal) basis is unitary. -/
