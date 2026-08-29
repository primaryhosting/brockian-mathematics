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

theorem nested_of_symm_convex_dim_one {K L : Set (Fin 1 → ℝ)}
    (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) :
    K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hyL
    have hxy : |y 0| ≤ |x 0| := by
      by_contra hcon
      push_neg at hcon
      exact hxL (mem_of_abs_le_of_symm_convex hL hLs hyL (le_of_lt hcon))
    exact mem_of_abs_le_of_symm_convex hK hKs hxK hxy

/-- Two subsets of a subsingleton type are nested. -/
