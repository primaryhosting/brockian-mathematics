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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation values of a symmetric operator are real. -/

lemma inner_commutator (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hcomm : A (B psi) - B (A psi) = ((hbar : ℂ) * Complex.I) • psi) :
    ⟪A psi, B psi⟫_ℂ - ⟪B psi, A psi⟫_ℂ = (hbar : ℂ) * Complex.I := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have h := congrArg (fun y : H => ⟪psi, y⟫_ℂ) hcomm
  simp only [inner_sub_right, inner_smul_right, hpp, mul_one] at h
  rw [hA psi (B psi), hB psi (A psi)]
  exact h

/-- **Heisenberg uncertainty principle.**  For symmetric (observable) operators `A`, `B`
on a complex inner product space satisfying the canonical commutation relation
`A (B ψ) - B (A ψ) = i ħ ψ` on a normalized state `ψ`, the product of the standard
deviations is at least `ħ / 2`.  The proof combines the commutator identity with the
Cauchy–Schwarz inequality (`norm_inner_le_norm`). -/
