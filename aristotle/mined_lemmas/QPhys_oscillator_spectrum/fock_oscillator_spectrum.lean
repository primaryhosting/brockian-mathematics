import RequestProject.Main

/-!
# A concrete model for the ladder-operator hypotheses

This file exhibits a concrete inner product space carrying ladder operators satisfying the
hypotheses of `QPhys.oscillator_spectrum`, so that the theorem is not vacuous.

The model is the algebraic Fock space of finitely supported complex sequences `ℕ →₀ ℂ`, with
`a (eₙ) = √n eₙ₋₁` and `a† (eₙ) = √(n+1) eₙ₊₁`.
-/

open scoped InnerProductSpace
open Finsupp

namespace QPhys

/-- The algebraic Fock space: finitely supported complex sequences. -/
abbrev FockSpace : Type := ℕ →₀ ℂ

namespace FockSpace

/-- The inner product on the algebraic Fock space. -/

theorem fock_oscillator_spectrum (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega) :
    {mu : ℂ | ∃ v : FockSpace, v ≠ 0 ∧ hamiltonian hbar omega v = mu • v}
      = {mu : ℂ | ∃ n : ℕ, mu = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)} :=
  QPhys.oscillator_spectrum annihilate create adjoint_rel ccr vacuum vacuum_ne_zero
    annihilate_vacuum hbar omega hhbar homega (hamiltonian hbar omega) (fun _ => rfl)

end FockSpace

end QPhys

import Mathlib
/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

set_option grind.warning false

namespace QPhys

open scoped InnerProductSpace

section Ladder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (a ad : V →ₗ[ℂ] V)

/-- The number operator `N = a† a`. -/
