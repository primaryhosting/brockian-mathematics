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
# A model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are not vacuous:
we build an explicit complex inner product space (the polynomials `ℂ[X]` with the
Bargmann–Fock inner product `⟪p, q⟫ = ∑ n ! * conj (pₙ) * qₙ`), two symmetric operators
`Xop`, `Pop` on it satisfying `[Xop, Pop] = 2 i`, and a normalized state.
-/

import Mathlib
import RequestProject.HeisenbergUncertainty

/-!
# A model for the canonical commutation relation (Bargmann–Fock space of polynomials)
-/

namespace QPhys

open Polynomial ComplexConjugate

/-- The Bargmann–Fock inner product on polynomials: `⟪p, q⟫ = ∑ₙ n! * conj pₙ * qₙ`. -/

lemma inner_im_eq {X P : H →ₗ[ℂ] H} (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    (hbar : ℝ) (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    (inner ℂ (X psi - ((mean X psi : ℝ) : ℂ) • psi)
        (P psi - ((mean P psi : ℝ) : ℂ) • psi) : ℂ).im = hbar / 2 := by
  set a : ℂ := ((mean X psi : ℝ) : ℂ) with ha
  set b : ℂ := ((mean P psi : ℝ) : ℂ) with hb
  set z : ℂ := inner ℂ (X psi - a • psi) (P psi - b • psi) with hz
  -- The commutator expectation value
  have hself : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have hcz : z - conj z = Complex.I * hbar := by
    have hzc : conj z = inner ℂ (P psi - b • psi) (X psi - a • psi) := by
      rw [hz, inner_conj_symm]
    have hXP : (inner ℂ (X psi) (P psi) : ℂ) = inner ℂ psi (X (P psi)) := hX psi (P psi)
    have hPX : (inner ℂ (P psi) (X psi) : ℂ) = inner ℂ psi (P (X psi)) := hP psi (X psi)
    have hXs : (inner ℂ (X psi) psi : ℂ) = inner ℂ psi (X psi) := hX psi psi
    have hPs : (inner ℂ (P psi) psi : ℂ) = inner ℂ psi (P psi) := hP psi psi
    have hcomm' : (inner ℂ psi (X (P psi)) : ℂ) - inner ℂ psi (P (X psi)) = Complex.I * hbar := by
      rw [← inner_sub_right, hcomm psi, inner_smul_right, hself, mul_one]
    rw [hz, hzc]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, ha, hb]
    rw [hXP, hPX, hXs, hPs, hself]
    linear_combination hcomm'
  have him := congrArg Complex.im hcz
  simp at him
  linarith

/-- **Heisenberg uncertainty principle.**  Let `X` and `P` be symmetric (self-adjoint)
operators on a complex inner product space satisfying the canonical commutation relation
`[X, P] = i ℏ`.  Then for every normalized state `ψ`, the product of the uncertainties
`Δx = ‖(X - ⟪X⟫)ψ‖` and `Δp = ‖(P - ⟪P⟫)ψ‖` satisfies `Δx · Δp ≥ ℏ/2`.

The proof combines the commutator identity with the Cauchy–Schwarz inequality
(`norm_inner_le_norm`). -/
