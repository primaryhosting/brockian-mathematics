import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The standard (centered, isotropic) Gaussian measure on `ℝ ^ n`, realized as the product of
`n` copies of the standard Gaussian measure on `ℝ`. -/

theorem subset_or_subset_one_dim {K L : Set (Fin 1 → ℝ)} (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hyL
    by_cases hle : |y 0| ≤ |x 0|
    · exact mem_of_abs_le_one_dim hK hKs hxK hle
    · exact absurd (mem_of_abs_le_one_dim hL hLs hyL (le_of_lt (not_le.mp hle))) hxL

/-- A Lean-checked reduction: in any dimension, the Gaussian correlation inequality holds for
a nested pair of sets, with no convexity or symmetry needed. -/
