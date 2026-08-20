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

theorem virial_theorem (H T W A : E →ₗ[ℂ] E) (ψ : E) (E₀ : ℝ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (heig : H ψ = (E₀ : ℂ) • ψ)
    (hcomm : ∀ x : E, H (A x) - A (H x) = (2 : ℂ) • T x - W x) :
    2 * inner ℂ ψ (T ψ) = inner ℂ ψ (W ψ) := by
  have key := inner_commutator_eq_zero H A ψ E₀ hsymm heig
  rw [hcomm ψ, inner_sub_right, inner_smul_right] at key
  linear_combination key

end Abstract

/-! ## The concrete one-dimensional Schrödinger commutator

We verify the commutator hypothesis of `Phys.virial_theorem` for the one-dimensional
Schrödinger operator `H = -½ d²/dx² + V`, with `T = -½ d²/dx²`, dilation generator
`A = x d/dx + ½` and virial `W = x V'(x)`. -/

section Concrete

/-- Kinetic energy operator in one dimension, `T = -½ d²/dx²`. -/
