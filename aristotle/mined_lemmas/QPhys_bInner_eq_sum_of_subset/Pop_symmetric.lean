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

lemma Pop_symmetric : IsSymmetricOp Pop := by
  intro u v
  simp only [inner_eq_bInner, Pop, LinearMap.smul_apply, LinearMap.sub_apply, aOp_apply,
    adOp_apply]
  have hl : bInner (Complex.I • (X * u - derivative u)) v
      = conj Complex.I * bInner (X * u - derivative u) v := bInner_smul_left _ _ _
  have hsub : ∀ a b c : ℂ[X], bInner (a - b) c = bInner a c - bInner b c := by
    intro a b c
    have := bInner_add_left (a - b) b c
    rw [sub_add_cancel] at this
    linear_combination -this
  rw [hl, hsub, bInner_X_mul_left, bInner_derivative_left]
  have hr : bInner u (Complex.I • (X * v - derivative v))
      = Complex.I * (bInner u (X * v) - bInner u (derivative v)) := by
    simp only [bInner, Polynomial.coeff_smul, Polynomial.coeff_sub, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hr]
  simp only [Complex.conj_I]
  ring

/-- The canonical commutation relation `[Xop, Pop] = 2 i` holds in this model. -/
