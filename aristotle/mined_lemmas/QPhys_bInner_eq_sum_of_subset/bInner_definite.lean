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

lemma bInner_definite (p : ℂ[X]) (h : bInner p p = 0) : p = 0 := by
  have hre : ∑ n ∈ p.support, (Nat.factorial n : ℝ) * Complex.normSq (p.coeff n) = 0 := by
    rw [← bInner_self_re, h, Complex.zero_re]
  have hz : ∀ n ∈ p.support, (Nat.factorial n : ℝ) * Complex.normSq (p.coeff n) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun n _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))).mp hre
  ext n
  by_cases hn : n ∈ p.support
  · have hzn := hz n hn
    have hf : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hnorm : Complex.normSq (p.coeff n) = 0 := by
      rcases mul_eq_zero.mp hzn with h1 | h2
      · exact absurd h1 hf
      · exact h2
    simpa using Complex.normSq_eq_zero.mp hnorm
  · simpa using Polynomial.notMem_support_iff.mp hn

/-- The Bargmann–Fock inner product turns `ℂ[X]` into an inner product space. -/
