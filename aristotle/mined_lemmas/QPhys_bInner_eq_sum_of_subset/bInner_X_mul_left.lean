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

lemma bInner_X_mul_left (p q : ℂ[X]) : bInner (X * p) q = bInner p (derivative q) := by
  set M := p.natDegree + 1 with hM
  have h1 : (X * p).support ⊆ Finset.range (M + 1) := by
    refine Polynomial.supp_subset_range ?_
    have := Polynomial.natDegree_mul_le (p := (X : ℂ[X])) (q := p)
    simp [Polynomial.natDegree_X] at this
    omega
  have h2 : p.support ⊆ Finset.range M := Polynomial.supp_subset_range (by omega)
  rw [bInner_eq_sum_of_subset h1 q, bInner_eq_sum_of_subset h2 (derivative q),
      Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
  have h0 : (Nat.factorial 0 : ℂ) * conj ((X * p).coeff 0) * q.coeff 0 = 0 := by simp
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hfac : (Nat.factorial (m + 1) : ℂ) = (m + 1) * (Nat.factorial m : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac]
  ring

/-- Differentiation is adjoint to multiplication by `X`. -/
