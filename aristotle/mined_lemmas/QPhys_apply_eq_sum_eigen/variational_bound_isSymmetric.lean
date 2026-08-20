/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

section

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an eigenbasis `b` of `H` with eigenvalues `E`. -/

theorem variational_bound_isSymmetric {H : V →ₗ[ℂ] V} (hsymm : H.IsSymmetric) (E₀ : ℝ)
    (hE₀ : ∀ μ : ℝ, Module.End.HasEigenvalue H (μ : ℂ) → E₀ ≤ μ) (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (⟪ψ, H ψ⟫_ℂ).re / (⟪ψ, ψ⟫_ℂ).re :=
  variational_bound (hsymm.eigenvectorBasis (n := Module.finrank ℂ V) rfl) H
    (hsymm.eigenvalues rfl) (fun i => hsymm.apply_eigenvectorBasis rfl i) E₀
    (fun i => hE₀ _ (hsymm.hasEigenvalue_eigenvalues rfl i)) ψ hψ

end Symmetric

end QPhys

