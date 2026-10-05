/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

open MeasureTheory

/-- A compactly supported function on `ℝ` vanishes at some point to the left of any given point. -/

theorem exists_le_apply_eq_zero {f : ℝ → ℝ} (hf : HasCompactSupport f) (x : ℝ) :
    ∃ a : ℝ, a ≤ x ∧ f a = 0 := by
  obtain ⟨b, hb⟩ := hf.isCompact.bddBelow
  refine ⟨min x (b - 1), min_le_left _ _, ?_⟩
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have hle : b ≤ min x (b - 1) := hb hmem
  have : min x (b - 1) ≤ b - 1 := min_le_right _ _
  linarith

/-- The one-dimensional base case of the Gagliardo–Nirenberg–Sobolev inequality:
for a compactly supported differentiable function on `ℝ` with integrable derivative,
the supremum norm is bounded by the `L¹` norm of the derivative. -/
