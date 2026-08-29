import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with finite-dimensional quantum systems, a state on `ℂⁿ` being described by a positive
semidefinite matrix `ρ : Matrix n n ℂ`.  Its fidelity with a second state `σ` is

`F(ρ, σ) = Tr √(√ρ σ √ρ)`,

which is `QI.fidelity`.

A *purification* of `ρ` in the doubled system `ℂⁿ ⊗ ℂⁿ` is a vector `u : n × n → ℂ` whose reduced
density matrix (partial trace over the second factor) is `ρ`; this is `QI.reducedDensity`.
`QI.uhlmann_fidelity` is Uhlmann's theorem: `F(ρ, σ)` is the *greatest* value of the overlap
`|⟪u, v⟫|` as `u` ranges over the purifications of `ρ` and `v` over those of `σ`.

The proof goes through the polar decomposition of a matrix (`QI.exists_unitary_polar`, proved
here from scratch by extending a linear isometry defined on a subspace) and the variational
characterisation of the trace norm (`QI.isGreatest_traceNorm`).
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

/-! ### An auxiliary extension lemma for linear isometries -/

/-- If `f g : E →ₗ[ℂ] E` satisfy `‖g x‖ = ‖f x‖` for all `x`, then there is a linear isometry `V`
of `E` with `V ∘ f = g`.  This is the key step in the polar decomposition. -/

theorem exists_linearIsometry_comp_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (f g : E →ₗ[ℂ] E) (h : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ V : E →ₗᵢ[ℂ] E, ∀ x, V (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hx0 : ‖g x‖ = 0 := by rw [h x]; simp [LinearMap.mem_ker.mp hx]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp hx0
  set g' : (E ⧸ LinearMap.ker f) →ₗ[ℂ] E := (LinearMap.ker f).liftQ g hker with hg'
  set L₀ : (LinearMap.range f) →ₗ[ℂ] E := g'.comp (f.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL₀
  have key : ∀ x : E, L₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have hq : f.quotKerEquivRange (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ := rfl
    rw [hL₀]
    simp only [LinearMap.comp_apply, ← hq, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  have hnorm : ∀ y : LinearMap.range f, ‖L₀ y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [key x]
    exact h x
  let L : (LinearMap.range f) →ₗᵢ[ℂ] E := ⟨L₀, hnorm⟩
  exact ⟨L.extend, fun x => (L.extend_apply ⟨f x, ⟨x, rfl⟩⟩).trans (key x)⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Polar decomposition -/

/-- **Polar decomposition** of a square complex matrix: every `M` can be written as
`√(M Mᴴ) * U` with `U` unitary. -/
