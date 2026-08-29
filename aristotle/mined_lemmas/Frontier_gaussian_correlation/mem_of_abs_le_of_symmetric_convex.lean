/-
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard Gaussian measure on `ℝ^n`, defined as the `n`-fold product of the
standard Gaussian measure on `ℝ`. -/

theorem mem_of_abs_le_of_symmetric_convex (S : Set ℝ) (hS : Convex ℝ S)
    (hsym : ∀ x ∈ S, -x ∈ S) {a b : ℝ} (ha : a ∈ S) (hab : |b| ≤ |a|) : b ∈ S := by
  refine hS.segment_subset (hsym a ha) ha ?_
  rw [segment_eq_uIcc, Set.mem_uIcc]
  rw [abs_le] at hab
  rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith [hab.1, hab.2]
  · right; constructor <;> linarith [hab.1, hab.2]

/-- Any two symmetric convex subsets of `ℝ` are nested: they are symmetric intervals
around the origin. -/
