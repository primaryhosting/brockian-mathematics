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

/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The header above is repeated here as a module docstring: Lean 4 does not allow a doc
comment to precede the import commands, so the first copy is a plain block comment.
-/

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Rayleigh quotients of a symmetric operator on a finite-dimensional space are bounded
below by `-‖H‖`, hence the set of Rayleigh quotients is bounded below. -/

theorem variational_bound [FiniteDimensional ℂ E] [Nontrivial E]
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (E₀ : ℝ)
    (hE₀ : ∀ μ : ℝ, Module.End.HasEigenvalue H (μ : ℂ) → E₀ ≤ μ)
    (ψ : E) (hψ : ψ ≠ 0) :
    E₀ ≤ RCLike.re (⟪ψ, H ψ⟫_ℂ) / RCLike.re (⟪ψ, ψ⟫_ℂ) := by
  set r : ℝ := ⨅ x : { x : E // x ≠ 0 },
    RCLike.re (⟪H (x : E), (x : E)⟫_ℂ) / ‖(x : E)‖ ^ 2 with hr
  have h1 : E₀ ≤ r := hE₀ r hH.hasEigenvalue_iInf_of_finiteDimensional
  have h2 : r ≤ RCLike.re (⟪H ψ, ψ⟫_ℂ) / ‖ψ‖ ^ 2 :=
    ciInf_le (bddBelow_rayleigh H) (⟨ψ, hψ⟩ : { x : E // x ≠ 0 })
  have hnum : RCLike.re (⟪H ψ, ψ⟫_ℂ) = RCLike.re (⟪ψ, H ψ⟫_ℂ) := by rw [hH ψ ψ]
  have hden : RCLike.re (⟪ψ, ψ⟫_ℂ) = ‖ψ‖ ^ 2 := inner_self_eq_norm_sq ψ
  rw [hnum] at h2
  rw [hden]
  linarith

end QPhys

