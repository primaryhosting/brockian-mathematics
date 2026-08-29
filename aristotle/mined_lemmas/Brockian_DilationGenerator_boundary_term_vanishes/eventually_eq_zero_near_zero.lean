/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- A function with compact support contained in `(0, ∞)` vanishes on a neighbourhood
of `0` (indeed on the whole of `(-∞, a)` for some `a > 0`). -/

theorem eventually_eq_zero_near_zero {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Set.Ioi 0) : ∃ a > 0, ∀ x < a, f x = 0 := by
  rcases Set.eq_empty_or_nonempty (tsupport f) with h | h
  · exact ⟨1, one_pos, fun x _ => image_eq_zero_of_notMem_tsupport (by simp [h])⟩
  · refine ⟨sInf (tsupport f), hsupp (hf.sInf_mem h), fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    exact absurd (csInf_le hf.bddBelow hmem) (not_le.mpr hx)

/-- A function with compact support vanishes far out to the right. -/
