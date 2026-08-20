/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
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

/-!
## Uhlmann's theorem

We work with finite-dimensional quantum systems, states being described by density
matrices (positive semidefinite matrices) on `ℂ^n`.

A *purification* of a state `ρ` on `ℂ^n` by an ancilla system `ℂ^m` is a vector
`ψ : n × m → ℂ` (i.e. an element of `ℂ^n ⊗ ℂ^m`) whose reduced state on the first
factor, `Tr_2 |ψ⟩⟨ψ|`, is `ρ`.

The *fidelity* of two states is `F(ρ, σ) = Tr √(√ρ σ √ρ)`.

Uhlmann's theorem states that `F(ρ, σ)` is the maximum of `|⟨ψ, ψ₂⟩|` over all
purifications `ψ` of `ρ` and `ψ₂` of `σ` (using an ancilla of the same dimension).
-/

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The partial trace over the second (ancilla) factor of `ℂ^n ⊗ ℂ^m`. -/

theorem exists_isometry_of_norm_eq (P M : Matrix n n ℂ)
    (hnorm : ∀ x : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin M x‖ = ‖Matrix.toEuclideanLin P x‖) :
    ∃ F : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ n,
      ∀ x, F (Matrix.toEuclideanLin P x) = Matrix.toEuclideanLin M x := by
  set p := Matrix.toEuclideanLin P with hp
  set m := Matrix.toEuclideanLin M with hm
  have hker : LinearMap.ker p ≤ LinearMap.ker m := by
    intro x hx
    have : ‖m x‖ = 0 := by rw [hnorm x, LinearMap.mem_ker.1 hx, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.1 this
  set q := (LinearMap.ker p).liftQ m hker with hq
  set e := p.quotKerEquivRange with he
  set f₀ : (LinearMap.range p) →ₗ[ℂ] EuclideanSpace ℂ n := q ∘ₗ (e.symm : _ →ₗ[ℂ] _) with hf0
  have hf₀ : ∀ x, f₀ ⟨p x, ⟨x, rfl⟩⟩ = m x := by
    intro x
    have hex : e (Submodule.Quotient.mk x) = ⟨p x, ⟨x, rfl⟩⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk p x)
    have hsymm : e.symm ⟨p x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x := by
      rw [← hex, LinearEquiv.symm_apply_apply]
    simp [hf0, hsymm, hq]
  have hnorm₀ : ∀ y : LinearMap.range p, ‖f₀ y‖ = ‖(y : EuclideanSpace ℂ n)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hf₀ x]
    exact hnorm x
  refine ⟨LinearIsometry.extend ⟨f₀, hnorm₀⟩, fun x => ?_⟩
  have := LinearIsometry.extend_apply (⟨f₀, hnorm₀⟩ : (LinearMap.range p) →ₗᵢ[ℂ] EuclideanSpace ℂ n)
    ⟨p x, ⟨x, rfl⟩⟩
  simpa [hf₀ x] using this

/-- **Polar decomposition**: every square complex matrix `M` factors as `M = Q * √(Mᴴ M)`
with `Q` unitary. -/
