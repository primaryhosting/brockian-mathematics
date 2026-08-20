/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`.
We take the real part; for a symmetric operator `A` the inner product is already real. -/

noncomputable def uncertainty (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - ((expectation A psi : ℝ) : ℂ) • psi‖

/-- **Heisenberg's uncertainty principle.**

Let `X` and `P` be symmetric (formally self-adjoint) operators on a complex inner product
space satisfying the canonical commutation relation `[X, P] = i ℏ` on all vectors, and let
`ψ` be a normalized state.  Then

  `Δx · Δp ≥ ℏ / 2`.

The proof is the classical one: writing `u = (X - ⟨X⟩)ψ`, `v = (P - ⟨P⟩)ψ`, the canonical
commutator gives `⟪u, v⟫ - ⟪v, u⟫ = i ℏ`, and the Cauchy–Schwarz inequality bounds the left
hand side in norm by `2 ‖u‖ ‖v‖ = 2 Δx Δp`. -/
