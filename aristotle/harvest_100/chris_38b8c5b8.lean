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

set_option autoImplicit false

namespace QPhys

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/
noncomputable def expectation (A : H →ₗ[ℂ] H) (ψ : H) : ℂ := inner ℂ ψ (A ψ)

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`. -/
noncomputable def stdDev (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖A ψ - expectation A ψ • ψ‖

/-- If the "commutator" `⟪u,v⟫ - ⟪v,u⟫` equals `c * i` for a real `c`, then
`c/2 ≤ ‖u‖ * ‖v‖`.  This is the Cauchy–Schwarz half of the uncertainty principle. -/
theorem half_le_norm_mul_norm_of_inner_sub_inner (u v : H) (c : ℝ)
    (h : inner ℂ u v - inner ℂ v u = (c : ℂ) * Complex.I) :
    c / 2 ≤ ‖u‖ * ‖v‖ := by
  have hconj : (starRingEnd ℂ) (inner ℂ u v) = inner ℂ v u := inner_conj_symm v u
  have hsub : (inner ℂ u v : ℂ) - (starRingEnd ℂ) (inner ℂ u v)
      = ((2 * (inner ℂ u v : ℂ).im : ℝ) : ℂ) * Complex.I := Complex.sub_conj _
  rw [hconj] at hsub
  rw [h] at hsub
  have him : c = 2 * (inner ℂ u v : ℂ).im := by
    have := mul_right_cancel₀ Complex.I_ne_zero hsub
    exact_mod_cast this
  have h1 : (inner ℂ u v : ℂ).im ≤ ‖(inner ℂ u v : ℂ)‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have h2 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have := h1.trans h2
  rw [him]
  linarith

/-- **Heisenberg uncertainty relation** (Robertson form for the canonical commutator).
If `X` and `P` are symmetric operators on a complex inner product space, `ψ` is a
normalized state, and the expectation of the canonical commutator `[X,P]` in the state
`ψ` equals `i ℏ`, then the product of the uncertainties of `X` and `P` in the state `ψ`
is at least `ℏ/2`. -/
theorem heisenberg_uncertainty (X P : H →ₗ[ℂ] H) (ψ : H) (hψ : ‖ψ‖ = 1)
    (hX : ∀ x y : H, inner ℂ (X x) y = inner ℂ x (X y))
    (hP : ∀ x y : H, inner ℂ (P x) y = inner ℂ x (P y))
    (hbar : ℝ)
    (hcomm : inner ℂ ψ (X (P ψ)) - inner ℂ ψ (P (X ψ)) = (hbar : ℂ) * Complex.I) :
    stdDev X ψ * stdDev P ψ ≥ hbar / 2 := by
  set a : ℂ := expectation X ψ with ha
  set b : ℂ := expectation P ψ with hb
  set u : H := X ψ - a • ψ with hu
  set v : H := P ψ - b • ψ with hv
  -- basic facts
  have hnorm : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have haX : (inner ℂ (X ψ) ψ : ℂ) = a := by rw [hX, ha, expectation]
  have hbP : (inner ℂ (P ψ) ψ : ℂ) = b := by rw [hP, hb, expectation]
  have huv : (inner ℂ u v : ℂ) = inner ℂ (X ψ) (P ψ) - a * b := by
    rw [hu, hv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hnorm, haX, hb, ha, expectation]
    ring
  have hvu : (inner ℂ v u : ℂ) = inner ℂ (P ψ) (X ψ) - b * a := by
    rw [hu, hv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hnorm, hbP, hb, ha, expectation]
    ring
  have key : (inner ℂ u v : ℂ) - inner ℂ v u = (hbar : ℂ) * Complex.I := by
    rw [huv, hvu, ← hcomm, hX, hP]
    ring
  have := half_le_norm_mul_norm_of_inner_sub_inner u v hbar key
  simpa [stdDev, hu, hv, ha, hb] using this

/-!
## Non-vacuity: an explicit instance of the hypotheses

The Pauli matrices `σx`, `σy` on the qubit space `EuclideanSpace ℂ (Fin 2)` are symmetric
and satisfy `⟪ψ, [σx, σy] ψ⟫ = 2 i` in the state `ψ = (1, 0)`, so the hypotheses of
`heisenberg_uncertainty` are satisfiable with `ℏ = 2`.
-/

/-- The Pauli `σx` observable on a qubit. -/
noncomputable def pauliX : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun v := WithLp.toLp 2 ![v 1, v 0]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

/-- The Pauli `σy` observable on a qubit. -/
noncomputable def pauliY : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun v := WithLp.toLp 2 ![-Complex.I * v 1, Complex.I * v 0]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

/-- The spin-up state of a qubit. -/
noncomputable def qubitUp : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]

theorem norm_qubitUp : ‖qubitUp‖ = 1 := by
  simp [qubitUp, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem pauliX_symm (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (pauliX x) y = inner ℂ x (pauliX y) := by
  simp [pauliX, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem pauliY_symm (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (pauliY x) y = inner ℂ x (pauliY y) := by
  simp [pauliY, PiLp.inner_apply, Fin.sum_univ_two, Complex.ext_iff]
  exact ⟨by ring, by ring⟩

theorem pauli_commutator_qubitUp :
    inner ℂ qubitUp (pauliX (pauliY qubitUp)) - inner ℂ qubitUp (pauliY (pauliX qubitUp))
      = ((2 : ℝ) : ℂ) * Complex.I := by
  simp [qubitUp, pauliX, pauliY, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- A concrete, non-vacuous instance of the uncertainty relation: for the spin-up qubit
state the product of the `σx` and `σy` uncertainties is at least `1 = ℏ/2` with `ℏ = 2`. -/
theorem heisenberg_uncertainty_qubit :
    stdDev pauliX qubitUp * stdDev pauliY qubitUp ≥ 1 := by
  have := heisenberg_uncertainty pauliX pauliY qubitUp norm_qubitUp pauliX_symm pauliY_symm 2
    pauli_commutator_qubitUp
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

