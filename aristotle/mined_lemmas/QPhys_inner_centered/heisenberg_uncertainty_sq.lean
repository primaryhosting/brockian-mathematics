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

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A (bounded, everywhere-defined) linear operator on a complex inner product space is
*symmetric* if it satisfies `⟪A u, v⟫ = ⟪u, A v⟫` for all vectors `u`, `v`. -/

theorem heisenberg_uncertainty_sq {X P : H →ₗ[ℂ] H} {ψ : H} (hbar : ℝ)
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P) (hψ : ‖ψ‖ = 1)
    (hcomm : ⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ = Complex.I * hbar) :
    spread X ψ ^ 2 * spread P ψ ^ 2 ≥ hbar ^ 2 / 4 := by
  have h1 : spread X ψ * spread P ψ ≥ hbar / 2 := heisenberg_uncertainty hbar hX hP hψ hcomm
  have h2 : spread X ψ * spread P ψ ≥ -hbar / 2 := by
    have hswap : spread P ψ * spread X ψ ≥ -hbar / 2 := by
      refine heisenberg_uncertainty (-hbar) hP hX hψ ?_
      have h3 : ⟪ψ, P (X ψ) - X (P ψ)⟫_ℂ = -⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ := by
        rw [← inner_neg_right]
        congr 1
        abel
      rw [h3, hcomm]
      push_cast
      ring
    rwa [mul_comm] at hswap
  have h5 : (hbar / 2) ^ 2 ≤ (spread X ψ * spread P ψ) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  calc hbar ^ 2 / 4 = (hbar / 2) ^ 2 := by ring
    _ ≤ (spread X ψ * spread P ψ) ^ 2 := h5
    _ = spread X ψ ^ 2 * spread P ψ ^ 2 := by ring


/-!
### Non-vacuity

The hypotheses of `QPhys.heisenberg_uncertainty` are satisfiable: the Pauli matrices `σx`, `σy`
acting on `ℂ²` are symmetric, and in the state `e₀` they satisfy `⟪ψ, (σx σy - σy σx) ψ⟫ = 2 i`.
-/

namespace Example

/-- The Pauli matrix `σx`. -/
