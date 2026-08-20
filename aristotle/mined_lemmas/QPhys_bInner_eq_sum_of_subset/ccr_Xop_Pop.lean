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

lemma ccr_Xop_Pop (u : ℂ[X]) : Xop (Pop u) - Pop (Xop u) = (Complex.I * ((2 : ℝ) : ℂ)) • u := by
  have hd : ∀ v : ℂ[X], derivative (X * v) = v + X * derivative v := by
    intro v
    rw [derivative_mul, derivative_X]
    ring
  simp only [Xop, Pop, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    aOp_apply, adOp_apply, map_smul, map_sub, derivative_add, derivative_mul, derivative_X,
    smul_sub, mul_add, smul_add]
  push_cast
  simp only [Polynomial.smul_eq_C_mul, map_mul, map_ofNat]
  ring

/-- The constant polynomial `1` is a normalized state. -/
