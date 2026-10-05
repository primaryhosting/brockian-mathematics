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

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem symmetricConvexReal_nested {K L : Set ℝ} (hKc : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K)
    (hLc : Convex ℝ L) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨a, haK, haL⟩ := Set.not_subset.mp h
    intro b hb
    have hba : |b| ≤ |a| := by
      by_contra hcon
      push_neg at hcon
      exact haL (memReal_of_abs_le hLc hLs hb (le_of_lt hcon))
    exact memReal_of_abs_le hKc hKs haK hba

/-- The Gaussian correlation inequality on the real line, for the one-dimensional standard
Gaussian measure `N(0,1)`. -/
