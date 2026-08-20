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
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator relation `[X, P] = i ℏ` evaluated in a normalized state `psi`:
the inner products `⟪X psi, P psi⟫` and `⟪P psi, X psi⟫` differ by `ℏ i`. -/

lemma inner_comm_diff (X P : E →ₗ[ℂ] E)
    (hXsymm : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hPsymm : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hbar : ℝ) (hcomm : ∀ u : E, X (P u) - P (X u) = ((hbar : ℂ) * Complex.I) • u)
    (psi : E) (hpsi : ‖psi‖ = 1) :
    ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = (hbar : ℂ) * Complex.I := by
  have h1 : ⟪X psi, P psi⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ := hXsymm _ _
  have h2 : ⟪P psi, X psi⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ := hPsymm _ _
  have hnorm : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  rw [h1, h2, ← inner_sub_right, hcomm psi, inner_smul_right, hnorm, mul_one]

/-- **Heisenberg uncertainty principle.**

For symmetric (self-adjoint) operators `X` and `P` on a complex inner product space
satisfying the canonical commutation relation `X P - P X = i ℏ`, and any normalized
state `psi`, the product of the standard deviations
`Δx = ‖(X - ⟨X⟩) psi‖` and `Δp = ‖(P - ⟨P⟩) psi‖` is at least `ℏ / 2`.

The proof is the classical one: the commutator forces the imaginary part of
`⟪(X - ⟨X⟩) psi, (P - ⟨P⟩) psi⟫` to be `ℏ / 2`, and Cauchy–Schwarz
(`norm_inner_le_norm`) bounds the modulus of that inner product by `Δx * Δp`. -/
