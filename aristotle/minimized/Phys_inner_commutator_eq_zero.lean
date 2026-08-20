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
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- the requested header, reproduced verbatim as a module docstring immediately after the import.)

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-! ## The abstract (operator) virial theorem -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- In a stationary state, the expectation value of any commutator with the Hamiltonian
vanishes: `⟨ψ, [H, A] ψ⟩ = 0` whenever `H` is symmetric and `H ψ = E₀ ψ` with `E₀` real. -/

lemma inner_commutator_eq_zero (H A : E →ₗ[ℂ] E) (ψ : E) (E₀ : ℝ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (heig : H ψ = (E₀ : ℂ) • ψ) :
    (inner ℂ ψ (H (A ψ) - A (H ψ)) : ℂ) = 0 := by
  rw [inner_sub_right, ← hsymm, heig]
  simp only [inner_smul_left, map_smul, inner_smul_right, Complex.conj_ofReal]
  ring

/-- **Quantum virial theorem.**

For a bound stationary state `ψ` of a symmetric Hamiltonian `H` with (real) energy `E₀`,
`H ψ = E₀ ψ`, and operators `T` (kinetic energy) and `W` (the virial `r · ∇V`) satisfying the
canonical commutator identity `[H, A] = 2T - W` for the dilation generator `A`
(`A = r · ∇ + d/2`, i.e. `i A = (r·p + p·r)/2`), one has `2⟨T⟩ = ⟨W⟩`. -/
