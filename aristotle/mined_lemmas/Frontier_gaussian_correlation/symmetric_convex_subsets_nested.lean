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

theorem symmetric_convex_subsets_nested (K L : Set ℝ) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.not_subset] at h1 h2
  obtain ⟨x, hxK, hxL⟩ := h1
  obtain ⟨y, hyL, hyK⟩ := h2
  rcases le_total |x| |y| with h | h
  · exact hxL (mem_of_abs_le_of_symmetric_convex L hL hLs hyL h)
  · exact hyK (mem_of_abs_le_of_symmetric_convex K hK hKs hxK h)

/-- Any two symmetric convex subsets of `ℝ¹` are nested. -/
