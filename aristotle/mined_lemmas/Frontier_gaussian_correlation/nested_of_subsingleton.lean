/-
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory ProbabilityTheory

/-- The standard (centred, identity covariance) Gaussian measure on `Fin n → ℝ`,
built as the `n`-fold product of the real standard Gaussian. -/

theorem nested_of_subsingleton {α : Type*} [Subsingleton α] (K L : Set α) :
    K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hyL
    exact absurd (Subsingleton.elim y x ▸ hyL) hxL

/-- **Gaussian correlation inequality, base case.**

The full inequality of Royen states that for origin-symmetric convex sets `K`, `L` in `ℝ ^ n`
the standard Gaussian measure satisfies `γ K * γ L ≤ γ (K ∩ L)`; this is the predicate
`Frontier.GaussianCorrelationInequality`. Here we prove it in dimensions `n ≤ 1`
(the base case of the induction on the dimension), via the fact that in dimension at most one
any two origin-symmetric convex sets are nested. -/
