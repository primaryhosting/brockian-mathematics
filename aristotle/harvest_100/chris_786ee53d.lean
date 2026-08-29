/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped TensorProduct

variable {𝕜 H : Type*} [Field 𝕜] [AddCommGroup H] [Module 𝕜 H]

/-- The (unnormalized) antisymmetric two-fermion state built from the single-particle
states `ψ` and `φ`: the Slater determinant `ψ ⊗ φ - φ ⊗ ψ` in `H ⊗[𝕜] H`. -/
noncomputable def antisymState (ψ φ : H) : H ⊗[𝕜] H := ψ ⊗ₜ[𝕜] φ - φ ⊗ₜ[𝕜] ψ

/-- Exchanging the two particles negates the antisymmetric state. -/
theorem antisymState_swap (ψ φ : H) :
    antisymState (𝕜 := 𝕜) φ ψ = -antisymState (𝕜 := 𝕜) ψ φ := by
  simp [antisymState]

/-- **Pauli exclusion principle.** A two-fermion antisymmetric state whose two
single-particle states are equal is the zero vector. -/
theorem pauli_exclusion_antisym (ψ : H) : antisymState (𝕜 := 𝕜) ψ ψ = 0 :=
  sub_self _

/-- Abstract form of the exclusion principle: any antisymmetric (in the sense of being
negated under exchange of its arguments) two-particle state assignment vanishes on the
diagonal, provided the scalars have characteristic `≠ 2`.  Here `sub_eq_zero` /
`neg_eq_self_iff` is the relevant Mathlib ingredient. -/
omit [AddCommGroup H] [Module 𝕜 H] in
theorem eq_zero_of_antisymm {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    (hchar : (2 : 𝕜) ≠ 0) (f : H → H → W) (hf : ∀ x y, f y x = -f x y) (ψ : H) :
    f ψ ψ = 0 := by
  have h : f ψ ψ = -f ψ ψ := hf ψ ψ
  have h2 : (2 : 𝕜) • f ψ ψ = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    simp
  simpa [smul_eq_zero, hchar] using h2

/-- The concrete Slater-determinant state is antisymmetric in the abstract sense, so the
Pauli exclusion principle also follows from `QPhys.eq_zero_of_antisymm`. -/
example (hchar : (2 : 𝕜) ≠ 0) (ψ : H) : antisymState (𝕜 := 𝕜) ψ ψ = 0 :=
  eq_zero_of_antisymm hchar _ (fun x y => antisymState_swap (𝕜 := 𝕜) x y) ψ

end QPhys

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

