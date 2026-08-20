import Mathlib
import RequestProject.Main

/-!
# A concrete model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are *consistent* with a
nonzero `ℏ`: we build the (algebraic) Fock space of finitely supported sequences `ℕ →₀ ℂ`
with the Bargmann inner product `⟪eₘ, eₙ⟫ = n! δₘₙ`, the annihilation and creation operators,
and the resulting position and momentum operators `X`, `P`, which are symmetric and satisfy
`X P - P X = i` (i.e. `ℏ = 1`).
-/

open scoped ComplexConjugate InnerProductSpace
open Finsupp

namespace QPhys

/-! ## The Bargmann inner product on `ℕ →₀ ℂ` -/

/-- The Bargmann inner product: `⟪f, g⟫ = ∑ₙ conj (f n) * g n * n!`. -/

theorem heisenberg_uncertainty_vacuum :
    ‖posOp vacuum - ⟪vacuum, posOp vacuum⟫_ℂ • vacuum‖ *
      ‖momOp vacuum - ⟪vacuum, momOp vacuum⟫_ℂ • vacuum‖ ≥ 1 / 2 := by
  have h := QPhys.heisenberg_uncertainty posOp momOp posOp_symmetric momOp_symmetric 1 vacuum
    norm_vacuum (by rw [posOp_momOp_commutator]; norm_num)
  simpa using h

end QPhys

#print axioms QPhys.canonical_commutation_satisfiable
#print axioms QPhys.heisenberg_uncertainty_vacuum

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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QPhys

/-!
## Setting

We work in an arbitrary complex inner product space `E` (the space of states).
Observables are symmetric (formally self-adjoint) `ℂ`-linear operators `X`, `P : E →ₗ[ℂ] E`.

For a state `psi`, the expectation value of an observable `X` is `⟪psi, X psi⟫_ℂ`, and the
standard deviation (the "uncertainty") is

`Δ X = ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖`,

which is the usual `√(⟪X²⟫ - ⟪X⟫²)` for a normalized state.

The only input beyond symmetry is the canonical commutation relation `[X, P] = i ℏ`
evaluated at the state, i.e. `X (P psi) - P (X psi) = (i * ℏ) • psi`.

Mathlib has no uncertainty principle; the proof below is the classical Robertson argument,
whose analytic core is the Cauchy–Schwarz inequality `norm_inner_le_norm`
(`Mathlib.Analysis.InnerProductSpace.Basic`).
-/

section Uncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expectation values of a symmetric operator are real. -/
