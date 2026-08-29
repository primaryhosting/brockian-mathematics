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

theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ u v : n × n → ℂ,
        reducedDensity u = ρ ∧ reducedDensity v = σ ∧ r = ‖overlap u v‖}
      (fidelity ρ σ) := by
  have hset : {r : ℝ | ∃ u v : n × n → ℂ,
        reducedDensity u = ρ ∧ reducedDensity v = σ ∧ r = ‖overlap u v‖}
      = {r : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ r = ‖(Aᴴ * B).trace‖} := by
    ext r
    constructor
    · rintro ⟨u, v, hu, hv, rfl⟩
      exact ⟨curryMat u, curryMat v, by rw [← reducedDensity_eq, hu],
        by rw [← reducedDensity_eq, hv], by rw [overlap_eq]⟩
    · rintro ⟨A, B, hA, hB, rfl⟩
      refine ⟨fun p => A p.1 p.2, fun p => B p.1 p.2, ?_, ?_, ?_⟩
      · rw [reducedDensity_eq, curryMat_uncurry, hA]
      · rw [reducedDensity_eq, curryMat_uncurry, hB]
      · rw [overlap_eq, curryMat_uncurry, curryMat_uncurry]
  rw [hset]
  exact uhlmann_fidelity_matrix hρ hσ

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

