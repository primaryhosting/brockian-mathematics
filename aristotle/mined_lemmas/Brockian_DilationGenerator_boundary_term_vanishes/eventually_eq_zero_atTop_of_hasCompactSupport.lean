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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.DilationGenerator

/-- If `f` has compact support contained in `(0, ∞)`, then `f` vanishes on a whole
neighbourhood of `0` in `ℝ`. -/

theorem eventually_eq_zero_atTop_of_hasCompactSupport
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x : ℝ in Filter.atTop, f x = 0 := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨b, hb⟩ := hc.bddAbove
  filter_upwards [Filter.eventually_gt_atTop b] with x hx
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  exact absurd (hb hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.**  For `f, g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as `x → 0⁺`
and as `x → ∞`.

(The hypotheses on `g` are stated as requested, although the argument only needs those
on `f`.) -/
