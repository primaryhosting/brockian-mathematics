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

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem subset_or_subset_of_isSymmConvex {K L : Set ℝ} (hK : IsSymmConvex K)
    (hL : IsSymmConvex L) : K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.not_subset] at h1 h2
  obtain ⟨a, haK, haL⟩ := h1
  obtain ⟨b, hbL, hbK⟩ := h2
  rcases le_total |a| |b| with h | h
  · exact haL (mem_of_abs_le_abs_of_isSymmConvex hL hbL h)
  · exact hbK (mem_of_abs_le_abs_of_isSymmConvex hK haK h)

/-- For a probability measure on `ℝ`, the correlation inequality holds for symmetric convex
sets, because two such sets are nested. -/
