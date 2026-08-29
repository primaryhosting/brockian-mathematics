/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open ComplexConjugate

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value of a symmetric operator in a state is real. -/
lemma conj_expectation (A : E →ₗ[ℂ] E) (hA : ∀ x y : E, inner ℂ (A x) y = inner ℂ x (A y))
    (psi : E) : conj (inner ℂ psi (A psi)) = inner ℂ psi (A psi) := by
  rw [inner_conj_symm (A psi) psi, hA]

/-- Expansion of the inner product of two vectors centred by (real) expectation values. -/
lemma inner_centred_expand (x y psi : E) (a b : ℂ) (hpp : (inner ℂ psi psi : ℂ) = 1)
    (hxp : (inner ℂ x psi : ℂ) = a) (hpy : (inner ℂ psi y : ℂ) = b) (hca : conj a = a) :
    (inner ℂ (x - a • psi) (y - b • psi) : ℂ) = inner ℂ x y - a * b := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hxp, hpy, hpp,
    hca]
  ring

/-- **Heisenberg uncertainty principle.**  For symmetric linear operators `A` and `B` on a
complex inner product space satisfying the canonical commutation relation `[A,B]ψ = i ħ ψ`
at a normalized state `ψ`, the product of the standard deviations
`Δ_A = ‖(A - ⟪ψ, Aψ⟫)ψ‖` and `Δ_B = ‖(B - ⟪ψ, Bψ⟫)ψ‖` is at least `ħ/2`. -/
theorem heisenberg_uncertainty (A B : E →ₗ[ℂ] E)
    (hA : ∀ x y : E, inner ℂ (A x) y = inner ℂ x (A y))
    (hB : ∀ x y : E, inner ℂ (B x) y = inner ℂ x (B y))
    (psi : E) (hpsi : ‖psi‖ = 1) (hbar : ℝ)
    (hcomm : A (B psi) - B (A psi) = ((hbar : ℂ) * Complex.I) • psi) :
    hbar / 2 ≤ ‖A psi - (inner ℂ psi (A psi)) • psi‖ * ‖B psi - (inner ℂ psi (B psi)) • psi‖ := by
  have hca : conj (inner ℂ psi (A psi) : ℂ) = inner ℂ psi (A psi) := conj_expectation A hA psi
  have hcb : conj (inner ℂ psi (B psi) : ℂ) = inner ℂ psi (B psi) := conj_expectation B hB psi
  have hpp : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hAp : (inner ℂ (A psi) psi : ℂ) = inner ℂ psi (A psi) := hA psi psi
  have hBp : (inner ℂ (B psi) psi : ℂ) = inner ℂ psi (B psi) := hB psi psi
  -- the centred vectors
  set u : E := A psi - (inner ℂ psi (A psi) : ℂ) • psi with hu
  set v : E := B psi - (inner ℂ psi (B psi) : ℂ) • psi with hv
  have h1 : (inner ℂ u v : ℂ)
      = inner ℂ (A psi) (B psi) - (inner ℂ psi (A psi) : ℂ) * (inner ℂ psi (B psi) : ℂ) :=
    inner_centred_expand _ _ _ _ _ hpp hAp rfl hca
  have h2 : conj (inner ℂ u v : ℂ)
      = inner ℂ (B psi) (A psi) - (inner ℂ psi (A psi) : ℂ) * (inner ℂ psi (B psi) : ℂ) := by
    rw [h1, map_sub, inner_conj_symm, map_mul, hca, hcb]
  have h3 : (inner ℂ (A psi) (B psi) : ℂ) - inner ℂ (B psi) (A psi)
      = inner ℂ psi (A (B psi) - B (A psi)) := by
    have e1 : (inner ℂ psi (A (B psi)) : ℂ) = inner ℂ (A psi) (B psi) := (hA psi (B psi)).symm
    have e2 : (inner ℂ psi (B (A psi)) : ℂ) = inner ℂ (B psi) (A psi) := (hB psi (A psi)).symm
    rw [inner_sub_right, e1, e2]
  have h4 : (inner ℂ psi (A (B psi) - B (A psi)) : ℂ) = (hbar : ℂ) * Complex.I := by
    rw [hcomm, inner_smul_right, hpp, mul_one]
  have hkey : (inner ℂ u v : ℂ) - conj (inner ℂ u v : ℂ) = (hbar : ℂ) * Complex.I := by
    rw [h2, h1, show (inner ℂ (A psi) (B psi) : ℂ)
        - (inner ℂ psi (A psi) : ℂ) * (inner ℂ psi (B psi) : ℂ)
        - ((inner ℂ (B psi) (A psi) : ℂ)
          - (inner ℂ psi (A psi) : ℂ) * (inner ℂ psi (B psi) : ℂ))
      = (inner ℂ (A psi) (B psi) : ℂ) - inner ℂ (B psi) (A psi) by ring, h3, h4]
  have him : (inner ℂ u v : ℂ).im = hbar / 2 := by
    rw [Complex.sub_conj] at hkey
    have h5 : ((2 * (inner ℂ u v : ℂ).im : ℝ) : ℂ) = (hbar : ℂ) :=
      mul_right_cancel₀ Complex.I_ne_zero hkey
    have h6 : 2 * (inner ℂ u v : ℂ).im = hbar := by exact_mod_cast h5
    linarith
  have h7 : |hbar / 2| ≤ ‖(inner ℂ u v : ℂ)‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h8 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm ..
  have h9 := le_abs_self (hbar / 2)
  linarith

end QPhys

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

