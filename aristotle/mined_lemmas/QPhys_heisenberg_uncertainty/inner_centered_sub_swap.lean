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

namespace QPhys

open ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

lemma inner_centered_sub_swap {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {psi : H} (hpsi : ‖psi‖ = 1) {hbar : ℝ}
    (hcomm : A (B psi) - B (A psi) = (Complex.I * hbar) • psi) :
    inner ℂ (centered A psi) (centered B psi) - inner ℂ (centered B psi) (centered A psi)
      = Complex.I * hbar := by
  have hnorm : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have h1 := inner_centered (B := B) hA hpsi
  have h2 := inner_centered (B := A) hB hpsi
  rw [h1, h2]
  have hc : (inner ℂ psi (A (B psi)) : ℂ) - inner ℂ psi (B (A psi)) = Complex.I * hbar := by
    rw [← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  have : expect A psi * expect B psi = expect B psi * expect A psi := by ring
  rw [this]
  linear_combination hc

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric (self-adjoint)
operators on a complex inner product space satisfying the canonical commutation relation
`[X, P] ψ = i ℏ ψ` on a normalized state `ψ`, then the product of the uncertainties
`Δx · Δp` is at least `ℏ / 2`. -/
